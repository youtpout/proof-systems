//! Dummy proof data for unverified (base-case / padding) proofs — port of
//! pickles' `dummy.ml`.
//!
//! A base-case step proof carries `should_finalize = false` unfinalized
//! entries and padding accumulators; their values are deterministic
//! ([`crate::ro`]) so the prover and every circuit agree on them. `sg` is the
//! commitment to the challenge polynomial of the dummy challenges
//! (`compute_sg` = a non-hiding commitment to `b_poly_coefficients`).

use ark_ff::PrimeField;

use crate::ro::Ro;

/// The dummy IPA challenges of one side: raw 128-bit prechallenges and their
/// endo field images (`Dummy.Ipa.{Step,Wrap}.challenges[_computed]`).
pub struct DummyIpa<F: PrimeField> {
    pub prechallenges: Vec<F>,
    pub challenges_computed: Vec<F>,
}

/// `rounds` dummy challenges from the shared 128-bit stream, with their
/// `to_field` images under `endo` (`Ipa.compute_challenge`).
pub fn ipa_challenges<F: PrimeField>(chal_stream: &mut Ro, rounds: usize, endo: F) -> DummyIpa<F> {
    let prechallenges: Vec<F> = (0..rounds).map(|_| chal_stream.next_field()).collect();
    let challenges_computed = prechallenges
        .iter()
        .map(|&c| crate::scalar_challenge::ScalarChallenge(c).to_field(endo))
        .collect();
    DummyIpa {
        prechallenges,
        challenges_computed,
    }
}

/// The dummy wrap-side (Tock, 15 rounds) and step-side (Tick, 16 rounds)
/// challenges, drawn from a single `"chal"` stream in that order (matching
/// `dummy.ml`'s module-initialisation order).
pub fn ipa_wrap_and_step<FWrap: PrimeField, FStep: PrimeField>(
    endo_wrap: FWrap,
    endo_step: FStep,
) -> (DummyIpa<FWrap>, DummyIpa<FStep>) {
    let mut chal = Ro::chal();
    let wrap = ipa_challenges(&mut chal, crate::common::TOCK_ROUNDS, endo_wrap);
    let step = ipa_challenges(&mut chal, crate::common::TICK_ROUNDS, endo_step);
    (wrap, step)
}

/// `compute_sg`: the challenge-polynomial commitment of the given (field-form)
/// challenges — a non-hiding SRS commitment to `b_poly_coefficients(chals)`.
pub fn compute_sg<G>(
    srs: &poly_commitment::ipa::SRS<G>,
    challenges_computed: &[G::ScalarField],
) -> G
where
    G: poly_commitment::commitment::CommitmentCurve,
{
    use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial};
    use poly_commitment::commitment::b_poly_coefficients;
    use poly_commitment::SRS as _;

    let coeffs = b_poly_coefficients(challenges_computed);
    let poly = DensePolynomial::from_coefficients_vec(coeffs);
    srs.commit_non_hiding(&poly, 1).chunks[0]
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Fq, Pallas, Vesta};
    use poly_commitment::commitment::b_poly_coefficients;
    use poly_commitment::SRS as _;

    /// The dummy challenge streams are deterministic and correctly sized, and
    /// `compute_sg` equals the direct MSM of the b-poly coefficients.
    #[test]
    fn dummy_challenges_and_sg() {
        let endo_wrap = <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1;
        let endo_step = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1;
        let (wrap, step) = ipa_wrap_and_step::<Fq, Fp>(endo_wrap, endo_step);
        assert_eq!(wrap.prechallenges.len(), crate::common::TOCK_ROUNDS);
        assert_eq!(step.prechallenges.len(), crate::common::TICK_ROUNDS);
        let (wrap2, _) = ipa_wrap_and_step::<Fq, Fp>(endo_wrap, endo_step);
        assert_eq!(wrap.prechallenges, wrap2.prechallenges, "deterministic");
        assert_ne!(
            wrap.prechallenges[0], wrap.prechallenges[1],
            "stream advances"
        );

        // sg == MSM of b_poly_coefficients over the SRS basis
        let srs = poly_commitment::ipa::SRS::<Pallas>::create(1 << crate::common::TOCK_ROUNDS);
        let sg = compute_sg(&srs, &wrap.challenges_computed);
        let coeffs = b_poly_coefficients(&wrap.challenges_computed);
        let expected =
            <Pallas as AffineRepr>::Group::msm(&srs.g[..coeffs.len()], &coeffs).unwrap();
        assert_eq!(sg, expected.into_affine());
        assert!(sg.is_on_curve());
    }
}
