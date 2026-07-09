//! Validated side-loaded Pickles verification keys.
//!
//! Side-loaded keys cross a trust boundary, so raw commitment coordinates and
//! branch metadata are checked before they can enter reduced messages.

use mina_curves::pasta::{Fp, Pallas};

use crate::{
    api::{wrap_verification_key_points, WrapCircuit},
    common::{actual_wrap_domain_size, TICK_ROUNDS},
    composition_types::{PlonkVerificationKeyEvals, ProofsVerified},
};

/// A wrap verification key together with the recursion metadata required to
/// select compatible step/wrap branches.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SideLoadedVerificationKey {
    pub step_domain_log2: u8,
    pub wrap_domain_log2: u8,
    pub proofs_verified: ProofsVerified,
    commitments: Vec<(Fp, Fp)>,
}

impl SideLoadedVerificationKey {
    pub const COMMITMENT_COUNT: usize = 28;

    pub fn new(
        step_domain_log2: u8,
        wrap_domain_log2: u8,
        proofs_verified: ProofsVerified,
        commitments: Vec<(Fp, Fp)>,
    ) -> Result<Self, SideLoadedKeyError> {
        let key = Self {
            step_domain_log2,
            wrap_domain_log2,
            proofs_verified,
            commitments,
        };
        key.validate()?;
        Ok(key)
    }

    pub fn from_wrap_verifier<const ROUNDS: usize, const STMT_LEN: usize>(
        step_domain_log2: u8,
        verifier: &snarky::api::VerifierIndexWrapper<WrapCircuit<ROUNDS, STMT_LEN>>,
    ) -> Result<Self, SideLoadedKeyError> {
        let wrap_domain_log2 = verifier.index.domain.log_size_of_group as u8;
        let proofs_verified = actual_wrap_domain_size(u32::from(wrap_domain_log2));
        Self::new(
            step_domain_log2,
            wrap_domain_log2,
            proofs_verified,
            wrap_verification_key_points(verifier),
        )
    }

    pub fn validate(&self) -> Result<(), SideLoadedKeyError> {
        if usize::from(self.step_domain_log2) > TICK_ROUNDS {
            return Err(SideLoadedKeyError::StepDomainTooLarge(
                self.step_domain_log2,
            ));
        }
        let domain_proofs = match self.wrap_domain_log2 {
            13 => ProofsVerified::N0,
            14 => ProofsVerified::N1,
            15 => ProofsVerified::N2,
            domain => return Err(SideLoadedKeyError::InvalidWrapDomain(domain)),
        };
        if domain_proofs != self.proofs_verified {
            return Err(SideLoadedKeyError::BranchDomainMismatch {
                proofs_verified: self.proofs_verified,
                wrap_domain_log2: self.wrap_domain_log2,
            });
        }
        if self.commitments.len() != Self::COMMITMENT_COUNT {
            return Err(SideLoadedKeyError::WrongCommitmentCount(
                self.commitments.len(),
            ));
        }
        for (index, &(x, y)) in self.commitments.iter().enumerate() {
            let point = Pallas::new_unchecked(x, y);
            if !point.is_on_curve() {
                return Err(SideLoadedKeyError::PointNotOnCurve(index));
            }
            if !point.is_in_correct_subgroup_assuming_on_curve() {
                return Err(SideLoadedKeyError::PointNotInSubgroup(index));
            }
        }
        Ok(())
    }

    pub fn commitments(&self) -> &[(Fp, Fp)] {
        &self.commitments
    }

    pub fn to_plonk_verification_key(
        &self,
    ) -> PlonkVerificationKeyEvals<(Fp, Fp)> {
        crate::reduced_messages::plonk_verification_key_from_list(&self.commitments)
    }

    pub fn ensure_compatible(
        &self,
        proofs_verified: ProofsVerified,
    ) -> Result<(), SideLoadedKeyError> {
        if self.proofs_verified == proofs_verified {
            Ok(())
        } else {
            Err(SideLoadedKeyError::ProofsVerifiedMismatch {
                key: self.proofs_verified,
                requested: proofs_verified,
            })
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SideLoadedKeyError {
    StepDomainTooLarge(u8),
    InvalidWrapDomain(u8),
    BranchDomainMismatch {
        proofs_verified: ProofsVerified,
        wrap_domain_log2: u8,
    },
    WrongCommitmentCount(usize),
    PointNotOnCurve(usize),
    PointNotInSubgroup(usize),
    ProofsVerifiedMismatch {
        key: ProofsVerified,
        requested: ProofsVerified,
    },
}

#[cfg(test)]
mod tests {
    use ark_ec::{AffineRepr, CurveGroup};
    use mina_curves::pasta::Fq;

    use super::*;

    fn valid_commitments() -> Vec<(Fp, Fp)> {
        (1..=SideLoadedVerificationKey::COMMITMENT_COUNT)
            .map(|scalar| {
                let point = (Pallas::generator() * Fq::from(scalar as u64)).into_affine();
                (point.x, point.y)
            })
            .collect()
    }

    #[test]
    fn validates_and_restores_the_canonical_vk_layout() {
        let points = valid_commitments();
        let key = SideLoadedVerificationKey::new(16, 14, ProofsVerified::N1, points.clone())
            .unwrap();
        assert_eq!(
            key.to_plonk_verification_key()
                .to_list()
                .into_iter()
                .copied()
                .collect::<Vec<_>>(),
            points
        );
        key.ensure_compatible(ProofsVerified::N1).unwrap();
    }

    #[test]
    fn rejects_invalid_curve_points_and_branch_metadata() {
        let mut points = valid_commitments();
        points[7] = (Fp::from(1u64), Fp::from(1u64));
        assert_eq!(
            SideLoadedVerificationKey::new(16, 14, ProofsVerified::N1, points).unwrap_err(),
            SideLoadedKeyError::PointNotOnCurve(7)
        );

        assert!(matches!(
            SideLoadedVerificationKey::new(
                16,
                13,
                ProofsVerified::N2,
                valid_commitments()
            ),
            Err(SideLoadedKeyError::BranchDomainMismatch { .. })
        ));
    }

    #[test]
    fn rejects_wrong_arity_and_oversized_step_domain() {
        let key =
            SideLoadedVerificationKey::new(16, 15, ProofsVerified::N2, valid_commitments())
                .unwrap();
        assert!(matches!(
            key.ensure_compatible(ProofsVerified::N1),
            Err(SideLoadedKeyError::ProofsVerifiedMismatch { .. })
        ));
        assert_eq!(
            SideLoadedVerificationKey::new(17, 15, ProofsVerified::N2, valid_commitments())
                .unwrap_err(),
            SideLoadedKeyError::StepDomainTooLarge(17)
        );
    }
}
