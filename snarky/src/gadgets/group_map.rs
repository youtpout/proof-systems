//! In-circuit hash-to-curve, the port of the OCaml `group_map` library
//! (and of Mina's `snarky_group_map/checked_map.ml`).
//!
//! This mirrors the SvdW06 construction of the out-of-circuit [groupmap]
//! crate, so the in-circuit result matches `groupmap::GroupMap::to_group`
//! exactly: three candidate x-coordinates are computed from the input, and
//! the first one that is a square is selected using witnessed
//! `is_square`/`sqrt` flags (the "Boneh trick": witness `y` such that
//! `y² = x` if `x` is a square, and `y² = m·x` for a fixed non-residue `m`
//! otherwise).

use std::borrow::Cow;

use ark_ec::short_weierstrass::SWCurveConfig;
use ark_ff::PrimeField;
use groupmap::BWParameters;

use crate::{
    constraint_system::BasicSnarkyConstraint,
    runner::Constraint,
    Boolean, FieldVar, RunState, SnarkyResult,
};

/// Finds the first quadratic non-residue of the field.
fn non_residue<F: PrimeField>() -> F {
    let mut i = F::from(2u64);
    loop {
        if i.legendre().is_qnr() {
            return i;
        }
        i += F::one();
    }
}

/// Division `a / b`, witnessing the quotient and constraining `q · b = a`.
/// Warning: if `b = 0`, the constraint is only satisfiable for `a = 0` (and
/// then `q` is unconstrained) — same semantics as the OCaml `Field.div`.
pub fn div_unsafe<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    a: &FieldVar<F>,
    b: &FieldVar<F>,
) -> SnarkyResult<FieldVar<F>> {
    let (a_clone, b_clone) = (a.clone(), b.clone());
    let q: FieldVar<F> = sys.compute(loc.clone(), move |env| {
        let a = env.read_var(&a_clone);
        let b = env.read_var(&b_clone);
        a * b.inverse().unwrap_or_else(F::zero)
    })?;
    sys.assert_r1cs(
        Some("div_unsafe".into()),
        loc,
        q.clone(),
        b.clone(),
        a.clone(),
    )?;
    Ok(q)
}

/// Witnesses `y = sqrt(x)` and constrains `y² = x`.
/// The witness generation panics if `x` is not a square.
pub fn sqrt_exn<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    x: &FieldVar<F>,
) -> SnarkyResult<FieldVar<F>> {
    let x_clone = x.clone();
    let y: FieldVar<F> = sys.compute(loc.clone(), move |env| {
        env.read_var(&x_clone)
            .sqrt()
            .expect("sqrt_exn: not a square")
    })?;
    // OCaml's `Field.Checked.sqrt` uses the dedicated Square constraint.
    // Encoding the same equation as a generic R1CS is sound but changes both
    // the Generic coefficients and how adjacent halves are packed.
    sys.add_constraint(
        Constraint::BasicSnarkyConstraint(BasicSnarkyConstraint::Square(
            y.clone(),
            x.clone(),
        )),
        Some("sqrt_exn".into()),
        loc,
    )?;
    Ok(y)
}

/// Returns `(sqrt(x or m·x), is_square(x))`, where `m` is a fixed
/// non-residue: exactly one of `x` and `m·x` is a square (for `x ≠ 0`).
pub fn sqrt_flagged<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    x: &FieldVar<F>,
) -> SnarkyResult<(FieldVar<F>, Boolean<F>)> {
    let x_clone = x.clone();
    let is_square: Boolean<F> = sys.compute(loc.clone(), move |env| {
        env.read_var(&x_clone).legendre().is_qr()
    })?;
    let m = non_residue::<F>();
    let to_root = sys.if_(loc.clone(), is_square.clone(), x.clone(), x.scale(m))?;
    let y = sqrt_exn(sys, loc, &to_root)?;
    Ok((y, is_square))
}

/// The three candidate x-coordinates for the input `t`, following the same
/// formulas as `groupmap::potential_xs`.
pub fn potential_xs<F, G>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    params: &BWParameters<G>,
    t: &FieldVar<F>,
) -> SnarkyResult<[FieldVar<F>; 3]>
where
    F: PrimeField,
    G: SWCurveConfig<BaseField = F>,
{
    let t2 = t.mul(t, None, loc.clone(), sys)?;

    // alpha = 1 / (t2 * (t2 + fu))
    let alpha_inv = t2.mul(
        &(&t2 + &FieldVar::constant(params.fu)),
        None,
        loc.clone(),
        sys,
    )?;
    let alpha = div_unsafe(sys, loc.clone(), &FieldVar::constant(F::one()), &alpha_inv)?;

    // x1 = sqrt(-3u² - u/2) - t2² * alpha * sqrt(-3u²)
    let t2_squared = t2.mul(&t2, None, loc.clone(), sys)?;
    let t2_squared_alpha = t2_squared.mul(&alpha, None, loc.clone(), sys)?;
    let x1 = &FieldVar::constant(params.sqrt_neg_three_u_squared_minus_u_over_2)
        - &t2_squared_alpha.scale(params.sqrt_neg_three_u_squared);

    // x2 = -u - x1
    let x2 = &FieldVar::constant(-params.u) - &x1;

    // x3 = u - (t2 + fu)² * (alpha * (t2 + fu)) / (3u²)
    let t2_plus_fu = &t2 + &FieldVar::constant(params.fu);
    let t2_inv = alpha.mul(&t2_plus_fu, None, loc.clone(), sys)?;
    let t2_plus_fu_squared = t2_plus_fu.mul(&t2_plus_fu, None, loc.clone(), sys)?;
    let temp = t2_plus_fu_squared.mul(&t2_inv, None, loc, sys)?;
    let x3 = &FieldVar::constant(params.u) - &temp.scale(params.inv_three_u_squared);

    Ok([x1, x2, x3])
}

/// Maps a field element to a point of the curve, in-circuit.
/// The result matches `groupmap::GroupMap::to_group` on the same input.
pub fn to_group<F, G>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    params: &BWParameters<G>,
    t: &FieldVar<F>,
) -> SnarkyResult<(FieldVar<F>, FieldVar<F>)>
where
    F: PrimeField,
    G: SWCurveConfig<BaseField = F>,
{
    let [x1, x2, x3] = potential_xs(sys, loc.clone(), params, t)?;

    let y_squared = |sys: &mut RunState<F>, x: &FieldVar<F>| -> SnarkyResult<FieldVar<F>> {
        // x³ + a·x + b
        let x_squared = x.mul(x, None, loc.clone(), sys)?;
        let x_cubed = x_squared.mul(x, None, loc.clone(), sys)?;
        Ok(&(&x_cubed + &x.scale(G::COEFF_A)) + &FieldVar::constant(G::COEFF_B))
    };

    let y1_squared = y_squared(sys, &x1)?;
    let y2_squared = y_squared(sys, &x2)?;
    let y3_squared = y_squared(sys, &x3)?;

    let (y1, b1) = sqrt_flagged(sys, loc.clone(), &y1_squared)?;
    let (y2, b2) = sqrt_flagged(sys, loc.clone(), &y2_squared)?;
    let (y3, b3) = sqrt_flagged(sys, loc.clone(), &y3_squared)?;

    // `Boolean.Assert.any [b1; b2; b3]` is implemented by OCaml as
    // `assert_non_zero (b1 + b2 + b3)`, i.e. one inverse R1CS.  Building a
    // Boolean with `Boolean::any` first would use Field.equal (two R1CS) and
    // only then assert the result, adding one superfluous nonlinear half.
    let candidates_sum = &(&b1.to_field_var() + &b2.to_field_var()) + &b3.to_field_var();
    let sum_for_witness = candidates_sum.clone();
    let candidates_sum_inv: FieldVar<F> = sys.compute(loc.clone(), move |env| {
        env.read_var(&sum_for_witness)
            .inverse()
            .unwrap_or_else(F::zero)
    })?;
    sys.assert_r1cs(
        Some("group-map any".into()),
        loc.clone(),
        candidates_sum_inv,
        candidates_sum,
        FieldVar::constant(F::one()),
    )?;

    let x1_is_first = b1.to_field_var();
    let x2_is_first = b1.not().and(&b2, sys, loc.clone()).to_field_var();
    let x3_is_first = b1
        .not()
        .and(&b2.not(), sys, loc.clone())
        .and(&b3, sys, loc.clone())
        .to_field_var();

    // x = x1_is_first * x1 + x2_is_first * x2 + x3_is_first * x3 (same for y)
    let mul =
        |a: &FieldVar<F>, b: &FieldVar<F>, sys: &mut RunState<F>| a.mul(b, None, loc.clone(), sys);
    let x = &(&mul(&x1_is_first, &x1, sys)? + &mul(&x2_is_first, &x2, sys)?)
        + &mul(&x3_is_first, &x3, sys)?;
    let y = &(&mul(&x1_is_first, &y1, sys)? + &mul(&x2_is_first, &y2, sys)?)
        + &mul(&x3_is_first, &y3, sys)?;

    Ok((x, y))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{api::SnarkyCircuit, loc};
    use ark_ff::UniformRand;
    use groupmap::GroupMap;
    use mina_curves::pasta::{Fp, PallasParameters, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { crate::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { crate::FULL_ROUNDS }>;

    struct TestCircuit {}

    impl SnarkyCircuit for TestCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { crate::FULL_ROUNDS }>;

        type PrivateInput = Fp;
        type PublicInput = ();
        /// The mapped Pallas point (x, y).
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>);

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let t: FieldVar<Fp> = sys.compute(loc!(), |_| *private.unwrap())?;
            let params = BWParameters::<PallasParameters>::setup();
            to_group(sys, loc!(), &params, &t)
        }
    }

    #[test]
    fn snarky_group_map_matches_out_of_circuit() {
        let test_circuit = TestCircuit {};
        let (mut prover_index, verifier_index) = test_circuit.compile_to_indexes().unwrap();

        let params = BWParameters::<PallasParameters>::setup();
        let mut rng = o1_utils::tests::make_test_rng(None);

        for _ in 0..2 {
            let t = Fp::rand(&mut rng);
            let expected = params.to_group(t);

            let (proof, public_output) = prover_index
                .prove::<BaseSponge, ScalarSponge>((), t, true)
                .unwrap();

            assert_eq!(*public_output, expected);
            verifier_index.verify::<BaseSponge, ScalarSponge>(proof, (), *public_output);
        }
    }
}
