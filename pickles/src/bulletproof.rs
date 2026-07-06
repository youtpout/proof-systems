//! In-circuit bulletproof / inner-product-argument verification pieces
//! (pickles' `check_bulletproof` and `Split_commitments.combine`), the second
//! half of `incrementally_verify_proof`.
//!
//! The commitments are combined with the polyscale challenge `xi` by Horner's
//! rule, scaling by `xi` through the endomorphism gadget
//! ([`crate::scalar_challenge::endo`]) exactly as pickles does — not by a full
//! scalar multiplication.

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{gadgets::curve::Point, FieldVar, RunState, SnarkyResult};

use crate::scalar_challenge::{endo, endo_inv};

/// Combines commitments by the polyscale challenge `xi`
/// (`Split_commitments.combine`): returns `Σ_i xi_field^i · C_i`, computed by
/// Horner's rule where each `xi·acc` is the endomorphism scalar multiplication
/// `endo(acc, xi)`.
///
/// `xi` is the 128-bit polyscale challenge (as squeezed); `endo_base` is the
/// curve's base endomorphism coefficient (for the `EndoMul` gate).
pub fn combine_commitments<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    commitments: &[Point<F>],
    xi: &FieldVar<F>,
    endo_base: F,
) -> SnarkyResult<Point<F>> {
    use crate::common::SCALAR_CHALLENGE_BITS;
    use crate::plonk_curve_ops::add_fast;

    let n = commitments.len();
    assert!(n > 0, "combine_commitments: empty commitments");
    // Horner from the highest-index commitment down:
    // acc = C_{n-1}; for i = n-2..0 { acc = C_i + xi·acc }
    let mut acc = commitments[n - 1].clone();
    for c in commitments[..n - 1].iter().rev() {
        let scaled = endo(sys, loc.clone(), &acc, xi, SCALAR_CHALLENGE_BITS, endo_base)?;
        acc = add_fast(sys, loc.clone(), c, &scaled)?;
    }
    Ok(acc)
}

/// The bulletproof reduction term sum (pickles' `bullet_reduce`, EC part):
/// given the per-round `(L, R)` points and the round prechallenges `pre`
/// (128-bit), returns `Σ_round (endo_inv(L, pre) + endo(R, pre))`
/// = `Σ_round (pre_field⁻¹·L + pre_field·R)`.
///
/// The sponge-driven derivation of the prechallenges is handled by the caller;
/// this is the pure elliptic-curve fold.
pub fn bullet_reduce_terms<F, C>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    lr: &[(Point<F>, Point<F>)],
    prechallenges: &[FieldVar<F>],
    endo_base: F,
    endo_scalar: <ark_ec::short_weierstrass::Affine<C> as ark_ec::AffineRepr>::ScalarField,
) -> SnarkyResult<Point<F>>
where
    F: PrimeField,
    C: ark_ec::short_weierstrass::SWCurveConfig<BaseField = F>,
{
    use crate::common::SCALAR_CHALLENGE_BITS;
    use crate::plonk_curve_ops::add_fast;

    assert_eq!(lr.len(), prechallenges.len());
    assert!(!lr.is_empty(), "bullet_reduce_terms: no rounds");

    let mut acc: Option<Point<F>> = None;
    for ((l, r), pre) in lr.iter().zip(prechallenges) {
        let left = endo_inv::<F, C>(
            sys,
            loc.clone(),
            l,
            pre,
            SCALAR_CHALLENGE_BITS,
            endo_base,
            endo_scalar,
        )?;
        let right = endo(sys, loc.clone(), r, pre, SCALAR_CHALLENGE_BITS, endo_base)?;
        let term = add_fast(sys, loc.clone(), &left, &right)?;
        acc = Some(match acc {
            None => term,
            Some(a) => add_fast(sys, loc.clone(), &a, &term)?,
        });
    }
    Ok(acc.unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::UniformRand;
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

    struct CombineCircuit {
        xi: u128,
        comms: Vec<(Fp, Fp)>,
    }
    impl SnarkyCircuit for CombineCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>);
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let xi: FieldVar<Fp> = sys.compute(loc!(), |_| Fp::from(self.xi))?;
            let mut comms = vec![];
            for &(x, y) in &self.comms {
                comms.push(Point::new(
                    sys.compute(loc!(), move |_| x)?,
                    sys.compute(loc!(), move |_| y)?,
                ));
            }
            let endo_base = crate::endo::tick::base();
            let acc = combine_commitments(sys, loc!(), &comms, &xi, endo_base)?;
            Ok((acc.x, acc.y))
        }
    }

    /// The in-circuit commitment combination equals the out-of-circuit
    /// `Σ xi_field^i · C_i` (Horner with the endo scalar).
    #[test]
    fn combine_commitments_matches_reference() {
        let mut rng = o1_utils::tests::make_test_rng(None);
        let (_, endo_scalar) = <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();

        for n in [1usize, 2, 4] {
            let comms: Vec<Pallas> = (0..n)
                .map(|_| (Pallas::generator() * Fq::rand(&mut rng)).into_affine())
                .collect();
            let xi = u128::rand(&mut rng);
            let xi_field = crate::scalar_challenge::ScalarChallenge(Fq::from(xi)).to_field(*endo_scalar);

            // reference: acc = C_{n-1}; for i=n-2..0 { acc = C_i + xi_field*acc }
            let mut acc = comms[n - 1].into_group();
            for c in comms[..n - 1].iter().rev() {
                acc = *c + acc * xi_field;
            }
            let expected = acc.into_affine();

            let circ = CombineCircuit {
                xi,
                comms: comms.iter().map(|c| (c.x, c.y)).collect(),
            };
            let (mut pi, ver) = circ.compile_to_indexes().unwrap();
            let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
            assert_eq!(*out, (expected.x, expected.y), "n = {n}");
            ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
        }
    }

    struct BulletReduceCircuit {
        prechallenges: Vec<u128>,
        lr: Vec<((Fp, Fp), (Fp, Fp))>,
    }
    impl SnarkyCircuit for BulletReduceCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>);
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let mkpt = |sys: &mut RunState<Fp>, p: (Fp, Fp)| -> SnarkyResult<Point<Fp>> {
                Ok(Point::new(
                    sys.compute(loc!(), move |_| p.0)?,
                    sys.compute(loc!(), move |_| p.1)?,
                ))
            };
            let mut lr = vec![];
            for &(l, r) in &self.lr {
                lr.push((mkpt(sys, l)?, mkpt(sys, r)?));
            }
            let mut pres = vec![];
            for &c in &self.prechallenges {
                pres.push(sys.compute(loc!(), move |_| Fp::from(c))?);
            }
            let acc = bullet_reduce_terms::<Fp, mina_curves::pasta::PallasParameters>(
                sys,
                loc!(),
                &lr,
                &pres,
                crate::endo::tick::base(),
                <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1,
            )?;
            Ok((acc.x, acc.y))
        }
    }

    /// bullet_reduce_terms equals Σ (pre_field⁻¹·L + pre_field·R).
    #[test]
    fn bullet_reduce_matches_reference() {
        let mut rng = o1_utils::tests::make_test_rng(None);
        let (_, endo_scalar) = <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();
        let rounds = 3;
        let lr_pts: Vec<(Pallas, Pallas)> = (0..rounds)
            .map(|_| {
                (
                    (Pallas::generator() * Fq::rand(&mut rng)).into_affine(),
                    (Pallas::generator() * Fq::rand(&mut rng)).into_affine(),
                )
            })
            .collect();
        let pres: Vec<u128> = (0..rounds).map(|_| u128::rand(&mut rng)).collect();

        // reference
        use ark_ff::Field;
        let mut acc = Pallas::zero().into_group();
        for (&(l, r), &pre) in lr_pts.iter().zip(&pres) {
            let pf = crate::scalar_challenge::ScalarChallenge(Fq::from(pre)).to_field(*endo_scalar);
            acc += l.into_group() * pf.inverse().unwrap() + r.into_group() * pf;
        }
        let expected = acc.into_affine();

        let circ = BulletReduceCircuit {
            prechallenges: pres,
            lr: lr_pts
                .iter()
                .map(|(l, r)| ((l.x, l.y), (r.x, r.y)))
                .collect(),
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        assert_eq!(*out, (expected.x, expected.y));
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }
}
