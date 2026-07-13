//! Scalar challenges and their endo-scalar interpretation
//! (port of pickles' `scalar_challenge.ml`).
//!
//! A scalar challenge is a 128-bit value `c` interpreted as a full scalar
//! through the curve endomorphism: `to_field(c) = 2 * (endo-fold of the bits
//! of c)`, matching kimchi's `ScalarChallenge::to_field`.

use ark_ff::{BigInteger, PrimeField};

use crate::common::SCALAR_CHALLENGE_BITS;

/// A 128-bit scalar challenge (out-of-circuit representation).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ScalarChallenge<F>(pub F);

impl<F: PrimeField> ScalarChallenge<F> {
    /// Interprets the challenge as a full field element via the
    /// endomorphism, exactly as kimchi's `ScalarChallenge::to_field`
    /// (`endo_coefficient` is the scalar endo of the proof's curve).
    pub fn to_field(&self, endo_coefficient: F) -> F {
        // same algorithm as kimchi::oracles / OCaml `Scalar_challenge.to_field`
        let bits = to_bits(self.0);
        let mut a = F::from(2u64);
        let mut b = F::from(2u64);
        for i in (0..SCALAR_CHALLENGE_BITS / 2).rev() {
            let r_2i = bits[2 * i];
            let s = if r_2i { F::one() } else { -F::one() };
            if bits[2 * i + 1] {
                a = a.double() + s;
                b = b.double();
            } else {
                a = a.double();
                b = b.double() + s;
            }
        }
        a * endo_coefficient + b
    }
}

fn to_bits<F: PrimeField>(x: F) -> Vec<bool> {
    let mut bits = x.into_bigint().to_bits_le();
    bits.truncate(SCALAR_CHALLENGE_BITS);
    bits.resize(SCALAR_CHALLENGE_BITS, false);
    bits
}

#[cfg(test)]
mod tests {
    use super::*;
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Vesta};

    /// Our to_field matches kimchi's ScalarChallenge::to_field.
    #[test]
    fn matches_kimchi_scalar_challenge() {
        use ark_ff::UniformRand;
        let mut rng = o1_utils::tests::make_test_rng(None);
        let (_, endo_r) = Vesta::endos();
        for _ in 0..10 {
            // sample a 128-bit challenge
            let c = Fp::from(u128::rand(&mut rng));
            let ours = ScalarChallenge(c).to_field(*endo_r);
            let kimchi = mina_poseidon::sponge::ScalarChallenge::new(c).to_field(endo_r);
            assert_eq!(ours, kimchi);
        }
    }
}

//
// In-circuit endo-scalar multiplication (the EndoMul gadget)
//

use std::borrow::Cow;

use snarky::{
    constraint_system::{EcEndoscaleInput, EndoscaleRound, EndoscaleScalarRound, KimchiConstraint},
    gadgets::curve::{add_complete, double, Point},
    runner::{Constraint, WitnessGeneration},
    FieldVar, RunState, SnarkyResult,
};

/// Multiplies the point `t` by the endo-interpretation of the `num_bits`-bit
/// challenge `scalar`, using the EndoMul gate (4 bits per row).
/// This is the port of pickles' `Scalar_challenge.endo`; the result equals
/// `[ScalarChallenge(scalar).to_field(endo_scalar)] * T` out of circuit.
pub fn endo<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    t: &Point<F>,
    scalar: &FieldVar<F>,
    num_bits: usize,
    endo_base: F,
) -> SnarkyResult<Point<F>> {
    assert_eq!(num_bits % 4, 0, "endo: num_bits must be a multiple of 4");
    let rows = num_bits / 4;

    let xt = t.x.seal(sys, loc.clone())?;
    let yt = t.y.seal(sys, loc.clone())?;

    // MSB-first bits of the scalar, as a witness helper
    let scalar_var = scalar.clone();
    let bit = move |env: &dyn snarky::runner::WitnessGeneration<F>, i: usize| -> F {
        let bits = env.read_var(&scalar_var).into_bigint().to_bits_le();
        if bits[num_bits - 1 - i] {
            F::one()
        } else {
            F::zero()
        }
    };

    // initial accumulator: p = (endo * xt, yt) + t ; acc = p + p
    // OCaml seals `Field.scale xt Endo.base` before using it as a point
    // coordinate, emitting `endo·xt - v = 0` in the (l, r) slots.
    let phi_x = xt.scale(endo_base).seal(sys, loc.clone())?;
    let phi_t = Point::new(phi_x, yt.clone());
    let p = add_complete(sys, loc.clone(), t, &phi_t)?;
    let mut acc = double(sys, loc.clone(), &p)?;

    let mut n_acc = FieldVar::zero();
    let mut state = Vec::with_capacity(rows);

    for i in 0..rows {
        let n_acc_prev = n_acc.clone();
        let b = |k: usize| {
            let bit = bit.clone();
            move |env: &dyn snarky::runner::WitnessGeneration<F>| bit(env, i * 4 + k)
        };
        let b1: FieldVar<F> = sys.compute(loc.clone(), b(0))?;
        let b2: FieldVar<F> = sys.compute(loc.clone(), b(1))?;
        let b3: FieldVar<F> = sys.compute(loc.clone(), b(2))?;
        let b4: FieldVar<F> = sys.compute(loc.clone(), b(3))?;

        let (xp, yp) = (acc.x.clone(), acc.y.clone());

        // helper: witness a value from previously-assigned vars
        macro_rules! w {
            (|$env:ident| $body:expr, [$($v:ident),*]) => {{
                $(let $v = $v.clone();)*
                let value: FieldVar<F> = sys.compute(loc.clone(), move |$env: &dyn snarky::runner::WitnessGeneration<F>| {
                    $(let $v = $env.read_var(&$v);)*
                    $body
                })?;
                value
            }};
        }
        let two = F::from(2u64);

        let xq1 = w!(
            |env| (F::one() + ((endo_base - F::one()) * b1)) * xt,
            [b1, xt]
        );
        let yq1 = w!(|env| (two * b2 - F::one()) * yt, [b2, yt]);
        let s1 = w!(
            |env| (yq1 - yp) * (xq1 - xp).inverse().unwrap(),
            [yq1, yp, xq1, xp]
        );
        let s1_squared = w!(|env| s1.square(), [s1]);
        let s2 = w!(
            |env| (yp.double() * (xp.double() + xq1 - s1_squared).inverse().unwrap()) - s1,
            [yp, xp, xq1, s1_squared, s1]
        );
        let xr = w!(|env| xq1 + s2.square() - s1_squared, [xq1, s2, s1_squared]);
        let yr = w!(|env| ((xp - xr) * s2) - yp, [xp, xr, s2, yp]);

        let xq2 = w!(
            |env| (F::one() + ((endo_base - F::one()) * b3)) * xt,
            [b3, xt]
        );
        let yq2 = w!(|env| (two * b4 - F::one()) * yt, [b4, yt]);
        let s3 = w!(
            |env| (yq2 - yr) * (xq2 - xr).inverse().unwrap(),
            [yq2, yr, xq2, xr]
        );
        let s3_squared = w!(|env| s3.square(), [s3]);
        let s4 = w!(
            |env| (yr.double() * (xr.double() + xq2 - s3_squared).inverse().unwrap()) - s3,
            [yr, xr, xq2, s3_squared, s3]
        );
        let xs = w!(|env| xq2 + s4.square() - s3_squared, [xq2, s4, s3_squared]);
        let ys = w!(|env| ((xr - xs) * s4) - yr, [xr, xs, s4, yr]);
        let inv = w!(
            |env| ((xp - xr) * (xr - xs)).inverse().unwrap(),
            [xp, xr, xs]
        );

        acc = Point::new(xs, ys);
        n_acc = w!(
            |env| {
                let mut n = n_acc_prev;
                for b in [b1, b2, b3, b4] {
                    n = n.double() + b;
                }
                n
            },
            [n_acc_prev, b1, b2, b3, b4]
        );

        state.push(EndoscaleRound {
            xt: xt.clone(),
            yt: yt.clone(),
            xp,
            yp,
            n_acc: n_acc_prev,
            xr,
            yr,
            s1,
            s3,
            b1,
            b2,
            b3,
            b4,
            inv,
        });
    }

    sys.add_constraint(
        Constraint::KimchiConstraint(KimchiConstraint::EcEndoscale(EcEndoscaleInput {
            state,
            xs: acc.x.clone(),
            ys: acc.y.clone(),
            n_acc: n_acc.clone(),
        })),
        Some("endo".into()),
        loc.clone(),
    )?;
    n_acc.assert_equals(sys, loc, scalar)?;

    Ok(acc)
}

/// Number of bits in a scalar challenge (pickles `Scalar_challenge.num_bits`).
pub const NUM_BITS: usize = 128;

/// `a` contribution of a 2-bit nybble in the endo-scalar fold (OCaml
/// `a_func`): `0,1 -> 0`, `2 -> -1`, `3 -> 1`.
fn a_func<F: PrimeField>(nybble: u64) -> F {
    match nybble {
        0 | 1 => F::zero(),
        2 => -F::one(),
        3 => F::one(),
        _ => unreachable!("nybble out of range"),
    }
}

/// `b` contribution of a 2-bit nybble (OCaml `b_func`): `0 -> -1`, `1 -> 1`,
/// `2,3 -> 0`.
fn b_func<F: PrimeField>(nybble: u64) -> F {
    match nybble {
        0 => -F::one(),
        1 => F::one(),
        2 | 3 => F::zero(),
        _ => unreachable!("nybble out of range"),
    }
}

/// In-circuit interpretation of a 128-bit scalar challenge as a full field
/// element via the endomorphism, using the `EndoMulScalar` gate — the port of
/// pickles' `Scalar_challenge.to_field_checked`. Returns `a * endo + b` and
/// constrains the recomposed challenge `n` to equal `scalar`.
///
/// Out of circuit this equals [`ScalarChallenge::to_field`] /
/// kimchi's `ScalarChallenge::to_field`.
pub fn scalar_to_field<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    scalar: &FieldVar<F>,
    endo: F,
) -> SnarkyResult<FieldVar<F>> {
    scalar_to_field_with_bits(sys, loc, scalar, endo, NUM_BITS)
}

/// Same as [`scalar_to_field`], but for the smaller dummy-challenge widths
/// used by o1js' Pickles bindings to force selector columns into every
/// compiled key.
pub fn scalar_to_field_with_bits<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    scalar: &FieldVar<F>,
    endo: F,
    num_bits: usize,
) -> SnarkyResult<FieldVar<F>> {
    let (a, b, n) = scalar_to_field_raw_with_bits(sys, loc.clone(), scalar, num_bits)?;
    n.assert_equals(sys, loc, scalar)?;

    Ok(&a.scale(endo) + &b)
}

/// Raw port of OCaml `Scalar_challenge.to_field_checked'`: emit the
/// `EndoMulScalar` rows and return `(a, b, n)`, without constraining
/// `n == scalar` and without combining `a * endo + b`.
pub fn scalar_to_field_raw_with_bits<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    scalar: &FieldVar<F>,
    num_bits: usize,
) -> SnarkyResult<(FieldVar<F>, FieldVar<F>, FieldVar<F>)> {
    const NYBBLES_PER_ROW: usize = 8;
    const BITS_PER_ROW: usize = 2 * NYBBLES_PER_ROW;
    assert_eq!(num_bits % BITS_PER_ROW, 0);
    let rows = num_bits / BITS_PER_ROW;

    // MSB-first bit `k` of the challenge witness (`bits_msb.(k)`).
    let scalar_msb = scalar.clone();
    assert!(num_bits <= F::MODULUS_BIT_SIZE as usize);
    let msb = move |env: &dyn WitnessGeneration<F>, k: usize| -> bool {
        let le = env.read_var(&scalar_msb).into_bigint().to_bits_le();
        le.get(num_bits - 1 - k).copied().unwrap_or(false)
    };

    let two = F::from(2u64);
    let mut a = FieldVar::constant(two);
    let mut b = FieldVar::constant(two);
    let mut n = FieldVar::zero();
    let mut state = Vec::with_capacity(rows);

    for i in 0..rows {
        let n0 = n.clone();
        let a0 = a.clone();
        let b0 = b.clone();

        // the 8 nybbles of this row, each in [0, 3]
        let mut xs = Vec::with_capacity(NYBBLES_PER_ROW);
        for j in 0..NYBBLES_PER_ROW {
            let msb = msb.clone();
            let xj: FieldVar<F> = sys.compute(loc.clone(), move |env| {
                let bit = BITS_PER_ROW * i + 2 * j;
                let b1 = u64::from(msb(env, bit)); // high bit of the nybble
                let b0 = u64::from(msb(env, bit + 1)); // low bit
                F::from(b0 + 2 * b1)
            })?;
            xs.push(xj);
        }

        // n8 = fold_j (4 * acc + nybble), starting from n0
        let n8: FieldVar<F> = {
            let (msb, n0c) = (msb.clone(), n0.clone());
            sys.compute(loc.clone(), move |env| {
                let mut acc = env.read_var(&n0c);
                for j in 0..NYBBLES_PER_ROW {
                    let bit = BITS_PER_ROW * i + 2 * j;
                    let nyb = u64::from(msb(env, bit + 1)) + 2 * u64::from(msb(env, bit));
                    acc = acc.double().double() + F::from(nyb);
                }
                acc
            })?
        };
        // a8 = fold_j (2 * acc + a_func(nybble)), starting from a0
        let a8: FieldVar<F> = {
            let (msb, a0c) = (msb.clone(), a0.clone());
            sys.compute(loc.clone(), move |env| {
                let mut acc = env.read_var(&a0c);
                for j in 0..NYBBLES_PER_ROW {
                    let bit = BITS_PER_ROW * i + 2 * j;
                    let nyb = u64::from(msb(env, bit + 1)) + 2 * u64::from(msb(env, bit));
                    acc = acc.double() + a_func::<F>(nyb);
                }
                acc
            })?
        };
        // b8 = fold_j (2 * acc + b_func(nybble)), starting from b0
        let b8: FieldVar<F> = {
            let (msb, b0c) = (msb.clone(), b0.clone());
            sys.compute(loc.clone(), move |env| {
                let mut acc = env.read_var(&b0c);
                for j in 0..NYBBLES_PER_ROW {
                    let bit = BITS_PER_ROW * i + 2 * j;
                    let nyb = u64::from(msb(env, bit + 1)) + 2 * u64::from(msb(env, bit));
                    acc = acc.double() + b_func::<F>(nyb);
                }
                acc
            })?
        };

        state.push(EndoscaleScalarRound {
            n0,
            n8: n8.clone(),
            a0,
            b0,
            a8: a8.clone(),
            b8: b8.clone(),
            x0: xs[0].clone(),
            x1: xs[1].clone(),
            x2: xs[2].clone(),
            x3: xs[3].clone(),
            x4: xs[4].clone(),
            x5: xs[5].clone(),
            x6: xs[6].clone(),
            x7: xs[7].clone(),
        });

        n = n8;
        a = a8;
        b = b8;
    }

    sys.add_constraint(
        Constraint::KimchiConstraint(KimchiConstraint::EcEndoscalar(state)),
        Some("scalar_to_field".into()),
        loc,
    )?;
    Ok((a, b, n))
}

#[cfg(test)]
mod scalar_to_field_tests {
    use super::*;
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;
    use snarky::{api::SnarkyCircuit, loc};

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    struct S2FCircuit {
        challenge: Fp,
        endo: Fp,
    }
    impl SnarkyCircuit for S2FCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        type PublicOutput = FieldVar<Fp>;
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<FieldVar<Fp>> {
            let c: FieldVar<Fp> = sys.compute(loc!(), |_| self.challenge)?;
            scalar_to_field(sys, loc!(), &c, self.endo)
        }
    }

    /// In-circuit scalar_to_field equals the out-of-circuit to_field / kimchi.
    #[test]
    fn scalar_to_field_matches_kimchi() {
        use ark_ff::UniformRand;
        let (_, endo_r) = Vesta::endos();
        let mut rng = o1_utils::tests::make_test_rng(None);
        for _ in 0..3 {
            let c = Fp::from(u128::rand(&mut rng));
            let expected = ScalarChallenge(c).to_field(*endo_r);
            let kimchi = mina_poseidon::sponge::ScalarChallenge::new(c).to_field(endo_r);
            assert_eq!(expected, kimchi);

            let circ = S2FCircuit {
                challenge: c,
                endo: *endo_r,
            };
            let (mut pi, ver) = circ.compile_to_indexes().unwrap();
            let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
            assert_eq!(
                *out, expected,
                "in-circuit scalar_to_field matches to_field"
            );
            ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
        }
    }
}

#[cfg(test)]
mod endo_tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Fq, Pallas, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;
    use snarky::{api::SnarkyCircuit, loc};

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    struct EndoCircuit {}

    impl SnarkyCircuit for EndoCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;

        /// (challenge, (t.x, t.y))
        type PrivateInput = (Fp, (Fp, Fp));
        type PublicInput = ();
        /// endo(t, challenge)
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>);

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let chal: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().0)?;
            let tx: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1 .0)?;
            let ty: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1 .1)?;

            let endo_base = crate::endo::tick::base();
            let t = Point::new(tx, ty);
            let res = endo(sys, loc!(), &t, &chal, SCALAR_CHALLENGE_BITS, endo_base)?;
            Ok((res.x, res.y))
        }
    }

    /// The endo gadget computes `[to_field(chal)] * T`, matching the
    /// out-of-circuit scalar multiplication.
    #[test]
    fn endo_gadget_matches_scalar_mul() {
        let circuit = EndoCircuit {};
        let (mut prover_index, verifier_index) = circuit.compile_to_indexes().unwrap();

        let mut rng = o1_utils::tests::make_test_rng(None);
        let (_, endo_scalar) = <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();

        for _ in 0..2 {
            use ark_ff::UniformRand;
            let chal_u128 = u128::rand(&mut rng);
            let t = (Pallas::generator() * Fq::rand(&mut rng)).into_affine();

            // expected: T * to_field(chal), with to_field over Pallas' scalar field
            let x = ScalarChallenge(Fq::from(chal_u128)).to_field(*endo_scalar);
            let expected = (t * x).into_affine();

            let private_input = (Fp::from(chal_u128), (t.x, t.y));
            let (proof, public_output) = prover_index
                .prove::<BaseSponge, ScalarSponge>((), private_input, true)
                .unwrap();

            assert_eq!(*public_output, (expected.x, expected.y));
            verifier_index.verify::<BaseSponge, ScalarSponge>(proof, (), *public_output);
        }
    }
}

/// Multiplies `g` by the *inverse* of the endo-interpretation of `chal`:
/// witnesses `res = [to_field(chal)]⁻¹ · g` out of circuit, then constrains
/// `endo(res, chal) = g`. Port of pickles' `Scalar_challenge.endo_inv`.
pub fn endo_inv<F, C>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    g: &Point<F>,
    chal: &FieldVar<F>,
    num_bits: usize,
    endo_base: F,
    endo_scalar: <ark_ec::short_weierstrass::Affine<C> as ark_ec::AffineRepr>::ScalarField,
) -> SnarkyResult<Point<F>>
where
    F: PrimeField,
    C: ark_ec::short_weierstrass::SWCurveConfig<BaseField = F>,
{
    use ark_ec::CurveGroup;
    use ark_ff::Field;

    let (gx, gy, chal_var) = (g.x.clone(), g.y.clone(), chal.clone());
    let res: (FieldVar<F>, FieldVar<F>) = sys.compute(
        loc.clone(),
        move |env: &dyn snarky::runner::WitnessGeneration<F>| {
            // read the challenge and reinterpret its low bits in the scalar field
            let chal_bits = env.read_var(&chal_var).into_bigint().to_bits_le();
            let one = C::ScalarField::from(1u64);
            let mut s = C::ScalarField::from(0u64);
            for i in (0..num_bits).rev() {
                s += s;
                if chal_bits[i] {
                    s += one;
                }
            }
            let x = ScalarChallenge(s).to_field(endo_scalar);
            let g = ark_ec::short_weierstrass::Affine::<C>::new_unchecked(
                env.read_var(&gx),
                env.read_var(&gy),
            );
            let res = (g * x.inverse().unwrap()).into_affine();
            (res.x, res.y)
        },
    )?;
    let res = Point::new(res.0, res.1);
    // OCaml witnesses `res` through `exists G.typ` (scalar_challenge.ml:263),
    // whose check asserts on-curve — one c=5 marker per bulletproof round.
    res.assert_on_curve(sys, loc.clone(), F::zero(), F::from(5u64))?;

    let mapped = endo(sys, loc.clone(), &res, chal, num_bits, endo_base)?;
    mapped.x.assert_equals(sys, loc.clone(), &g.x)?;
    mapped.y.assert_equals(sys, loc, &g.y)?;

    Ok(res)
}

#[cfg(test)]
mod endo_inv_tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::Field;
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Fq, Pallas, PallasParameters, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;
    use snarky::{api::SnarkyCircuit, loc};

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    struct EndoInvCircuit {}

    impl SnarkyCircuit for EndoInvCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;

        type PrivateInput = (Fp, (Fp, Fp));
        type PublicInput = ();
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>);

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let chal: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().0)?;
            let gx: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1 .0)?;
            let gy: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1 .1)?;

            let (_, endo_scalar) = <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();
            let g = Point::new(gx, gy);
            let res = endo_inv::<Fp, PallasParameters>(
                sys,
                loc!(),
                &g,
                &chal,
                SCALAR_CHALLENGE_BITS,
                crate::endo::tick::base(),
                *endo_scalar,
            )?;
            Ok((res.x, res.y))
        }
    }

    /// `endo_inv(g, chal)` == `[to_field(chal)]⁻¹ · g`.
    #[test]
    fn endo_inv_matches_scalar_mul() {
        let circuit = EndoInvCircuit {};
        let (mut prover_index, verifier_index) = circuit.compile_to_indexes().unwrap();

        let mut rng = o1_utils::tests::make_test_rng(None);
        let (_, endo_scalar) = <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();

        use ark_ff::UniformRand;
        let chal_u128 = u128::rand(&mut rng);
        let g = (Pallas::generator() * Fq::rand(&mut rng)).into_affine();

        let x = ScalarChallenge(Fq::from(chal_u128)).to_field(*endo_scalar);
        let expected = (g * x.inverse().unwrap()).into_affine();

        let private_input = (Fp::from(chal_u128), (g.x, g.y));
        let (proof, public_output) = prover_index
            .prove::<BaseSponge, ScalarSponge>((), private_input, true)
            .unwrap();

        assert_eq!(*public_output, (expected.x, expected.y));
        verifier_index.verify::<BaseSponge, ScalarSponge>(proof, (), *public_output);
    }
}
