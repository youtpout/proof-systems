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
    constraint_system::{EcEndoscaleInput, EndoscaleRound, KimchiConstraint},
    gadgets::curve::{add_complete, double, Point},
    runner::Constraint,
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
    let phi_t = Point::new(xt.scale(endo_base), yt.clone());
    let p = add_complete(sys, loc.clone(), &phi_t, t)?;
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
