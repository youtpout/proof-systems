//! Validated side-loaded Pickles verification keys.
//!
//! Side-loaded keys cross a trust boundary, so raw commitment coordinates and
//! branch metadata are checked before they can enter reduced messages.

use ark_ff::{BigInteger, PrimeField};
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
    pub const MINA_FIELD_BYTES: usize = 32;
    pub const MINA_PAYLOAD_FIELDS: usize = 3 + 2 * Self::COMMITMENT_COUNT;
    pub const MINA_PAYLOAD_BYTES: usize = Self::MINA_PAYLOAD_FIELDS * Self::MINA_FIELD_BYTES;

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

    /// Circuit-facing Mina field order: step domain, wrap domain,
    /// proofs-verified, then the 28 commitment `(x,y)` pairs in canonical VK
    /// order. This representation is independent of Rust struct layout.
    pub fn to_mina_field_elements(&self) -> Vec<Fp> {
        let mut fields = Vec::with_capacity(Self::MINA_PAYLOAD_FIELDS);
        fields.push(Fp::from(u64::from(self.step_domain_log2)));
        fields.push(Fp::from(u64::from(self.wrap_domain_log2)));
        fields.push(Fp::from(self.proofs_verified.to_usize() as u64));
        for &(x, y) in &self.commitments {
            fields.push(x);
            fields.push(y);
        }
        fields
    }

    /// Canonical 32-byte little-endian encoding of
    /// [`Self::to_mina_field_elements`]. Field values are never reduced while
    /// decoding: non-canonical encodings are rejected.
    pub fn to_mina_field_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(Self::MINA_PAYLOAD_BYTES);
        for field in self.to_mina_field_elements() {
            let mut encoded = field.into_bigint().to_bytes_le();
            encoded.resize(Self::MINA_FIELD_BYTES, 0);
            bytes.extend(encoded);
        }
        bytes
    }

    pub fn from_mina_field_bytes(bytes: &[u8]) -> Result<Self, SideLoadedKeyError> {
        if bytes.len() != Self::MINA_PAYLOAD_BYTES {
            return Err(SideLoadedKeyError::WrongSerializedLength(bytes.len()));
        }
        let mut fields = Vec::with_capacity(Self::MINA_PAYLOAD_FIELDS);
        for (index, chunk) in bytes.chunks_exact(Self::MINA_FIELD_BYTES).enumerate() {
            let bits = chunk
                .iter()
                .flat_map(|byte| (0..8).map(move |bit| byte & (1 << bit) != 0))
                .collect::<Vec<_>>();
            let bigint = <Fp as PrimeField>::BigInt::from_bits_le(&bits);
            let field =
                Fp::from_bigint(bigint).ok_or(SideLoadedKeyError::NonCanonicalField(index))?;
            fields.push(field);
        }

        let decode_u8 = |index: usize| -> Result<u8, SideLoadedKeyError> {
            (0..=u8::MAX)
                .find(|value| fields[index] == Fp::from(u64::from(*value)))
                .ok_or(SideLoadedKeyError::InvalidMetadataField(index))
        };
        let step_domain_log2 = decode_u8(0)?;
        let wrap_domain_log2 = decode_u8(1)?;
        let proofs_verified = match decode_u8(2)? {
            0 => ProofsVerified::N0,
            1 => ProofsVerified::N1,
            2 => ProofsVerified::N2,
            _ => return Err(SideLoadedKeyError::InvalidMetadataField(2)),
        };
        let commitments = fields[3..]
            .chunks_exact(2)
            .map(|point| (point[0], point[1]))
            .collect();
        Self::new(
            step_domain_log2,
            wrap_domain_log2,
            proofs_verified,
            commitments,
        )
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
    WrongSerializedLength(usize),
    NonCanonicalField(usize),
    InvalidMetadataField(usize),
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

    #[test]
    fn mina_field_encoding_is_stable_and_round_trips() {
        let key =
            SideLoadedVerificationKey::new(16, 14, ProofsVerified::N1, valid_commitments())
                .unwrap();
        let bytes = key.to_mina_field_bytes();
        assert_eq!(bytes.len(), SideLoadedVerificationKey::MINA_PAYLOAD_BYTES);
        assert_eq!(&bytes[..4], &[16, 0, 0, 0]);
        assert_eq!(
            &bytes[SideLoadedVerificationKey::MINA_FIELD_BYTES
                ..SideLoadedVerificationKey::MINA_FIELD_BYTES + 4],
            &[14, 0, 0, 0]
        );
        assert_eq!(
            &bytes[2 * SideLoadedVerificationKey::MINA_FIELD_BYTES
                ..2 * SideLoadedVerificationKey::MINA_FIELD_BYTES + 4],
            &[1, 0, 0, 0]
        );
        assert_eq!(
            SideLoadedVerificationKey::from_mina_field_bytes(&bytes).unwrap(),
            key
        );
    }

    #[test]
    fn mina_field_encoding_rejects_malleable_inputs() {
        assert_eq!(
            SideLoadedVerificationKey::from_mina_field_bytes(&[0; 12]).unwrap_err(),
            SideLoadedKeyError::WrongSerializedLength(12)
        );

        let key =
            SideLoadedVerificationKey::new(16, 14, ProofsVerified::N1, valid_commitments())
                .unwrap();
        let mut bytes = key.to_mina_field_bytes();
        bytes[..SideLoadedVerificationKey::MINA_FIELD_BYTES].fill(0xff);
        assert_eq!(
            SideLoadedVerificationKey::from_mina_field_bytes(&bytes).unwrap_err(),
            SideLoadedKeyError::NonCanonicalField(0)
        );
    }
}
