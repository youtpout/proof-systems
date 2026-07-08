//! Wire-sized messages passed between proofs over the same field.
//!
//! These mirror Mina's
//! `reduced_messages_for_next_proof_over_same_field.ml`: the step form omits
//! the globally-known wrap verification key, while `prepare` converts raw IPA
//! prechallenges to scalar-field challenges.

use ark_ff::PrimeField;

use crate::composition_types::{
    wrap::MessagesForNextWrapProof, BulletproofChallenge, MessagesForNextStepProof,
    PlonkVerificationKeyEvals,
};
use crate::ipa::compute_challenges;
use crate::scalar_challenge::ScalarChallenge;

/// Restores the typed Pickles verification-key layout from its canonical
/// 28-commitment flattened order.
pub fn plonk_verification_key_from_list<Comm: Clone>(
    points: &[Comm],
) -> PlonkVerificationKeyEvals<Comm> {
    assert_eq!(points.len(), 28, "Pickles verification key has 28 points");
    PlonkVerificationKeyEvals {
        sigma_comm: points[0..7].to_vec(),
        coefficients_comm: points[7..22].to_vec(),
        generic_comm: points[22].clone(),
        psm_comm: points[23].clone(),
        complete_add_comm: points[24].clone(),
        mul_comm: points[25].clone(),
        emul_comm: points[26].clone(),
        endomul_scalar_comm: points[27].clone(),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step<S, Comm, RawChallenges> {
    pub app_state: S,
    pub challenge_polynomial_commitments: Vec<Comm>,
    pub old_bulletproof_challenges: Vec<Vec<RawChallenges>>,
}

impl<S, Comm: Clone, RawChallenges: Clone> Step<S, Comm, RawChallenges> {
    /// Front-pads previous-proof entries to Pickles' fixed maximum width.
    pub fn pad_front_to(
        mut self,
        width: usize,
        dummy_commitment: Comm,
        dummy_challenges: Vec<RawChallenges>,
    ) -> Self {
        assert!(self.challenge_polynomial_commitments.len() <= width);
        assert_eq!(
            self.challenge_polynomial_commitments.len(),
            self.old_bulletproof_challenges.len()
        );
        let padding = width - self.challenge_polynomial_commitments.len();
        self.challenge_polynomial_commitments
            .splice(0..0, std::iter::repeat_n(dummy_commitment, padding));
        self.old_bulletproof_challenges
            .splice(0..0, std::iter::repeat_n(dummy_challenges, padding));
        self
    }
}

impl<S, Comm, F: PrimeField> Step<S, Comm, BulletproofChallenge<ScalarChallenge<F>>> {
    pub fn prepare(
        self,
        dlog_plonk_index: PlonkVerificationKeyEvals<Comm>,
        endo_scalar: F,
    ) -> MessagesForNextStepProof<Comm, S, Vec<Comm>, Vec<Vec<F>>> {
        let old_bulletproof_challenges = self
            .old_bulletproof_challenges
            .iter()
            .map(|chals| compute_challenges(chals, endo_scalar))
            .collect();
        MessagesForNextStepProof {
            app_state: self.app_state,
            dlog_plonk_index,
            challenge_polynomial_commitments: self.challenge_polynomial_commitments,
            old_bulletproof_challenges,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Wrap<Comm, RawChallenges> {
    pub challenge_polynomial_commitment: Comm,
    pub old_bulletproof_challenges: Vec<Vec<RawChallenges>>,
}

impl<Comm, RawChallenges: Clone> Wrap<Comm, RawChallenges> {
    pub fn pad_challenges_front_to(
        mut self,
        width: usize,
        dummy_challenges: Vec<RawChallenges>,
    ) -> Self {
        assert!(self.old_bulletproof_challenges.len() <= width);
        let padding = width - self.old_bulletproof_challenges.len();
        self.old_bulletproof_challenges
            .splice(0..0, std::iter::repeat_n(dummy_challenges, padding));
        self
    }
}

impl<Comm, F: PrimeField> Wrap<Comm, BulletproofChallenge<ScalarChallenge<F>>> {
    pub fn prepare(self, endo_scalar: F) -> MessagesForNextWrapProof<Comm, Vec<Vec<F>>> {
        MessagesForNextWrapProof {
            challenge_polynomial_commitment: self.challenge_polynomial_commitment,
            old_bulletproof_challenges: self
                .old_bulletproof_challenges
                .iter()
                .map(|chals| compute_challenges(chals, endo_scalar))
                .collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fq, Pallas};

    fn raw(x: u64) -> BulletproofChallenge<ScalarChallenge<Fq>> {
        BulletproofChallenge {
            prechallenge: ScalarChallenge(Fq::from(x)),
        }
    }

    #[test]
    fn wrap_prepare_computes_challenges_and_preserves_commitment() {
        let endo = <Pallas as KimchiCurve<{ crate::common::FULL_ROUNDS }>>::endos().1;
        let reduced = Wrap {
            challenge_polynomial_commitment: (Fq::from(7u64), Fq::from(8u64)),
            old_bulletproof_challenges: vec![vec![raw(1), raw(2)]],
        };
        let prepared = reduced.prepare(endo);
        assert_eq!(
            prepared.challenge_polynomial_commitment,
            (Fq::from(7u64), Fq::from(8u64))
        );
        assert_eq!(
            prepared.old_bulletproof_challenges[0],
            vec![
                ScalarChallenge(Fq::from(1u64)).to_field(endo),
                ScalarChallenge(Fq::from(2u64)).to_field(endo),
            ]
        );
    }

    #[test]
    fn verification_key_flat_order_round_trips() {
        let points: Vec<u64> = (0..28).collect();
        let vk = plonk_verification_key_from_list(&points);
        assert_eq!(
            vk.to_list().into_iter().copied().collect::<Vec<_>>(),
            points
        );
    }

    #[test]
    fn reduced_messages_front_padding_preserves_real_suffix() {
        let step = Step {
            app_state: (),
            challenge_polynomial_commitments: vec![9u64],
            old_bulletproof_challenges: vec![vec![8u64]],
        }
        .pad_front_to(2, 1, vec![2]);
        assert_eq!(step.challenge_polynomial_commitments, vec![1, 9]);
        assert_eq!(step.old_bulletproof_challenges, vec![vec![2], vec![8]]);

        let wrap = Wrap {
            challenge_polynomial_commitment: 7u64,
            old_bulletproof_challenges: vec![vec![8u64]],
        }
        .pad_challenges_front_to(2, vec![2]);
        assert_eq!(wrap.old_bulletproof_challenges, vec![vec![2], vec![8]]);
    }
}
