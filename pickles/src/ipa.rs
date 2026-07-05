//! Inner-product-argument helpers shared by the pickles verifiers
//! (port of the `challenge_polynomial` of `wrap_verifier.ml` and the
//! `Ipa.compute_challenge(s)` of `common.ml`).

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{FieldVar, RunState, SnarkyResult};

use crate::composition_types::BulletproofChallenge;
use crate::scalar_challenge::ScalarChallenge;

/// Converts an IPA prechallenge to its field form via the endomorphism
/// (`Ipa.compute_challenge`).
pub fn compute_challenge<F: PrimeField>(
    prechallenge: &BulletproofChallenge<ScalarChallenge<F>>,
    endo_scalar: F,
) -> F {
    prechallenge.prechallenge.to_field(endo_scalar)
}

/// Converts all IPA prechallenges (`Ipa.compute_challenges`).
pub fn compute_challenges<F: PrimeField>(
    prechallenges: &[BulletproofChallenge<ScalarChallenge<F>>],
    endo_scalar: F,
) -> Vec<F> {
    prechallenges
        .iter()
        .map(|c| compute_challenge(c, endo_scalar))
        .collect()
}

/// Evaluates the IPA challenge polynomial
/// `prod_i (1 + chals[i] * pt^{2^{k-1-i}})` out of circuit.
pub fn challenge_polynomial<F: PrimeField>(chals: &[F], pt: F) -> F {
    let k = chals.len();
    // pow_two_pows[i] = pt^{2^i}
    let mut pow_two_pows = vec![pt; k];
    for i in 1..k {
        pow_two_pows[i] = pow_two_pows[i - 1].square();
    }
    let mut res = F::one();
    for (i, c) in chals.iter().enumerate() {
        res *= F::one() + *c * pow_two_pows[k - 1 - i];
    }
    res
}

/// In-circuit evaluation of the IPA challenge polynomial — the core of the
/// `b` check in `finalize_other_proof`.
pub fn challenge_polynomial_circuit<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    chals: &[FieldVar<F>],
    pt: &FieldVar<F>,
) -> SnarkyResult<FieldVar<F>> {
    let k = chals.len();
    // pow_two_pows[i] = pt^{2^i}
    let mut pow_two_pows = vec![pt.clone()];
    for i in 1..k {
        let prev = &pow_two_pows[i - 1];
        pow_two_pows.push(prev.mul(prev, None, loc.clone(), sys)?);
    }
    // product of the terms 1 + chals[i] * pt^{2^{k-1-i}}
    let mut res = FieldVar::constant(F::one());
    for (i, c) in chals.iter().enumerate() {
        let scaled = c.mul(&pow_two_pows[k - 1 - i], None, loc.clone(), sys)?;
        let term = &FieldVar::constant(F::one()) + &scaled;
        res = res.mul(&term, None, loc.clone(), sys)?;
    }
    Ok(res)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::TOCK_ROUNDS;
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;
    use snarky::{api::SnarkyCircuit, loc, RunState};

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    const K: usize = TOCK_ROUNDS;

    struct BPolyCircuit {}

    impl SnarkyCircuit for BPolyCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;

        /// (challenges, evaluation point)
        type PrivateInput = ([Fp; K], Fp);
        type PublicInput = ();
        type PublicOutput = FieldVar<Fp>;

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let chals: [FieldVar<Fp>; K] = sys.compute(loc!(), |_| private.unwrap().0)?;
            let pt: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1)?;
            challenge_polynomial_circuit(sys, loc!(), &chals, &pt)
        }
    }

    /// The in-circuit challenge polynomial equals the out-of-circuit one,
    /// on challenges derived from real prechallenges.
    #[test]
    fn challenge_polynomial_parity() {
        let circuit = BPolyCircuit {};
        let (mut prover_index, verifier_index) = circuit.compile_to_indexes().unwrap();

        let mut rng = o1_utils::tests::make_test_rng(None);
        let (_, endo_scalar) = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();

        use ark_ff::UniformRand;
        // challenges as they would come out of an IPA transcript
        let prechallenges: Vec<_> = (0..K)
            .map(|_| BulletproofChallenge {
                prechallenge: ScalarChallenge(Fp::from(u128::rand(&mut rng))),
            })
            .collect();
        let chals: [Fp; K] = compute_challenges(&prechallenges, *endo_scalar)
            .try_into()
            .unwrap();
        let pt = Fp::rand(&mut rng);

        let expected = challenge_polynomial(&chals, pt);

        let (proof, public_output) = prover_index
            .prove::<BaseSponge, ScalarSponge>((), (chals, pt), true)
            .unwrap();

        assert_eq!(*public_output, expected);
        verifier_index.verify::<BaseSponge, ScalarSponge>(proof, (), *public_output);
    }
}
