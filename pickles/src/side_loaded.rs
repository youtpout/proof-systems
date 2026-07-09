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
    pub max_proofs_verified: ProofsVerified,
    pub proofs_verified: ProofsVerified,
    commitments: Vec<(Fp, Fp)>,
}

/// Raw circuit witness form. Unlike [`SideLoadedVerificationKey`], this type
/// may contain invalid data so the circuit can prove that malformed
/// side-loaded keys are rejected by constraints.
#[derive(Clone, Debug)]
pub struct SideLoadedKeyWitness {
    pub step_domain_log2: u8,
    pub wrap_domain_log2: u8,
    pub proofs_verified: u8,
    pub commitments: [(Fp, Fp); SideLoadedVerificationKey::COMMITMENT_COUNT],
}

impl From<&SideLoadedVerificationKey> for SideLoadedKeyWitness {
    fn from(key: &SideLoadedVerificationKey) -> Self {
        Self {
            step_domain_log2: key.step_domain_log2,
            wrap_domain_log2: key.wrap_domain_log2,
            proofs_verified: key.proofs_verified.to_usize() as u8,
            commitments: key
                .commitments
                .clone()
                .try_into()
                .unwrap_or_else(|_| unreachable!("validated key has 28 commitments")),
        }
    }
}

impl SideLoadedVerificationKey {
    pub const COMMITMENT_COUNT: usize = 28;
    pub const MINA_FIELD_BYTES: usize = 32;
    pub const MINA_PAYLOAD_FIELDS: usize = 6 + 2 * Self::COMMITMENT_COUNT;
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
            max_proofs_verified: proofs_verified,
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
        if self.max_proofs_verified.to_usize() < self.proofs_verified.to_usize() {
            return Err(SideLoadedKeyError::ActualWidthExceedsMaximum);
        }
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

    /// Mina `to_input` field order: one-hot `max_proofs_verified`, one-hot
    /// `actual_wrap_domain_size`, then the 28 commitment `(x,y)` pairs.
    pub fn to_mina_field_elements(&self) -> Vec<Fp> {
        let mut fields = Vec::with_capacity(Self::MINA_PAYLOAD_FIELDS);
        let one_hot = |proofs: ProofsVerified| {
            std::array::from_fn::<Fp, 3, _>(|index| {
                Fp::from(u64::from(index == proofs.to_usize()))
            })
        };
        fields.extend(one_hot(self.max_proofs_verified));
        fields.extend(one_hot(self.proofs_verified));
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

        let decode_one_hot = |offset: usize| -> Result<ProofsVerified, SideLoadedKeyError> {
            let bits = &fields[offset..offset + 3];
            (0..3)
                .find(|&selected| {
                    bits.iter().enumerate().all(|(index, value)| {
                        *value == Fp::from(u64::from(index == selected))
                    })
                })
                .map(ProofsVerified::from_usize)
                .ok_or(SideLoadedKeyError::InvalidMetadataField(offset))
        };
        let max_proofs_verified = decode_one_hot(0)?;
        let proofs_verified = decode_one_hot(3)?;
        let commitments = fields[6..]
            .chunks_exact(2)
            .map(|point| (point[0], point[1]))
            .collect();
        let wrap_domain_log2 =
            crate::common::wrap_domain_log2(proofs_verified.to_usize()) as u8;
        let mut key = Self::new(
            crate::common::TICK_ROUNDS as u8,
            wrap_domain_log2,
            proofs_verified,
            commitments,
        )?;
        key.max_proofs_verified = max_proofs_verified;
        Ok(key)
    }

    /// Convert this validated key to Mina's
    /// `Side_loaded_verification_key.Stable.V2` wire layout.
    ///
    /// Mina's Stable.V2 representation carries the maximum and actual wrap
    /// arities plus the 28 Plonk commitments. It does not carry the step
    /// domain, so the inverse conversion requires that metadata explicitly.
    pub fn to_stable_v2(&self) -> crate::mina_bin_prot::SideLoadedVerificationKeyV2 {
        crate::mina_bin_prot::SideLoadedVerificationKeyV2 {
            max_proofs_verified: self.max_proofs_verified,
            actual_wrap_domain_size: self.proofs_verified,
            commitments: self.commitments.clone(),
        }
    }

    pub fn from_stable_v2(
        step_domain_log2: u8,
        key: crate::mina_bin_prot::SideLoadedVerificationKeyV2,
    ) -> Result<Self, SideLoadedKeyError> {
        let wrap_domain_log2 =
            crate::common::wrap_domain_log2(key.actual_wrap_domain_size.to_usize()) as u8;
        let key = Self {
            step_domain_log2,
            wrap_domain_log2,
            max_proofs_verified: key.max_proofs_verified,
            proofs_verified: key.actual_wrap_domain_size,
            commitments: key.commitments,
        };
        key.validate()?;
        Ok(key)
    }

    pub fn to_stable_v2_base58(
        &self,
    ) -> Result<String, crate::mina_bin_prot::BinProtError> {
        self.to_stable_v2().to_base58_check()
    }

    pub fn from_stable_v2_base58(
        step_domain_log2: u8,
        value: &str,
    ) -> Result<Self, SideLoadedStableV2Error> {
        let key =
            crate::mina_bin_prot::SideLoadedVerificationKeyV2::from_base58_check(value)?;
        Ok(Self::from_stable_v2(step_domain_log2, key)?)
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
    ActualWidthExceedsMaximum,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SideLoadedStableV2Error {
    Codec(crate::mina_bin_prot::BinProtError),
    Key(SideLoadedKeyError),
}

impl From<crate::mina_bin_prot::BinProtError> for SideLoadedStableV2Error {
    fn from(error: crate::mina_bin_prot::BinProtError) -> Self {
        Self::Codec(error)
    }
}

impl From<SideLoadedKeyError> for SideLoadedStableV2Error {
    fn from(error: SideLoadedKeyError) -> Self {
        Self::Key(error)
    }
}

#[cfg(test)]
mod tests {
    use ark_ec::{AffineRepr, CurveGroup};
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::Fq;
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use snarky::{api::SnarkyCircuit, loc, FieldVar, RunState, SnarkyResult};

    use super::*;
    use crate::{
        api::{SideLoadedStepCircuit, StepApp},
        common::FULL_ROUNDS,
        inductive_rule::{InductiveRule, RuleId},
    };

    type BaseSponge = DefaultFqSponge<
        mina_curves::pasta::VestaParameters,
        PlonkSpongeConstantsKimchi,
        FULL_ROUNDS,
    >;
    type ScalarSponge =
        DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

    #[derive(Clone, Copy)]
    struct IdentityApp;

    impl StepApp for IdentityApp {
        type Witness = Fp;

        fn main(
            &self,
            sys: &mut RunState<Fp>,
            witness: Option<&Fp>,
        ) -> SnarkyResult<Vec<FieldVar<Fp>>> {
            Ok(vec![sys.compute(loc!(), |_| *witness.unwrap())?])
        }

        fn state(&self, witness: &Fp) -> Vec<Fp> {
            vec![*witness]
        }
    }

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
        assert_eq!(&bytes[..4], &[0, 0, 0, 0]);
        assert_eq!(
            &bytes[SideLoadedVerificationKey::MINA_FIELD_BYTES
                ..SideLoadedVerificationKey::MINA_FIELD_BYTES + 4],
            &[1, 0, 0, 0]
        );
        assert_eq!(
            &bytes[2 * SideLoadedVerificationKey::MINA_FIELD_BYTES
                ..2 * SideLoadedVerificationKey::MINA_FIELD_BYTES + 4],
            &[0, 0, 0, 0]
        );
        let decoded = SideLoadedVerificationKey::from_mina_field_bytes(&bytes).unwrap();
        assert_eq!(decoded.commitments, key.commitments);
        assert_eq!(decoded.max_proofs_verified, ProofsVerified::N1);
        assert_eq!(decoded.proofs_verified, ProofsVerified::N1);
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

    #[test]
    fn stable_v2_conversion_round_trips_through_mina_base58() {
        let key =
            SideLoadedVerificationKey::new(16, 15, ProofsVerified::N2, valid_commitments())
                .unwrap();
        let base58 = key.to_stable_v2_base58().unwrap();
        let decoded = SideLoadedVerificationKey::from_stable_v2_base58(16, &base58).unwrap();

        assert_eq!(decoded, key);
        assert_eq!(decoded.to_mina_field_elements(), key.to_mina_field_elements());
        assert_eq!(decoded.to_stable_v2(), key.to_stable_v2());
    }

    #[test]
    fn stable_v2_conversion_rejects_invalid_metadata() {
        let stable = crate::mina_bin_prot::SideLoadedVerificationKeyV2 {
            max_proofs_verified: ProofsVerified::N1,
            actual_wrap_domain_size: ProofsVerified::N2,
            commitments: valid_commitments(),
        };

        assert_eq!(
            SideLoadedVerificationKey::from_stable_v2(16, stable).unwrap_err(),
            SideLoadedKeyError::ActualWidthExceedsMaximum
        );
    }

    #[test]
    fn side_loaded_step_circuit_accepts_valid_key_and_rejects_tampering() {
        let key =
            SideLoadedVerificationKey::new(9, 13, ProofsVerified::N0, valid_commitments())
                .unwrap();
        let rule = InductiveRule::new(RuleId(0), "base", ProofsVerified::N0, 9);
        let circuit = SideLoadedStepCircuit {
            app: IdentityApp,
            rule,
        };
        let (mut prover, verifier) = circuit.compile_to_indexes().unwrap();
        let app_state = vec![Fp::from(42u64)];
        let digest = crate::hash_messages::hash_messages_for_next_step_proof_ref(
            mina_curves::pasta::Vesta::sponge_params(),
            key.commitments(),
            &app_state,
            &[],
            &[],
        );
        let witness = SideLoadedKeyWitness::from(&key);
        let (proof, _) = prover
            .prove::<BaseSponge, ScalarSponge>(
                digest,
                (Fp::from(42u64), witness.clone()),
                true,
            )
            .unwrap();
        verifier.verify::<BaseSponge, ScalarSponge>(proof, digest, ());

        let mut invalid_point = witness.clone();
        invalid_point.commitments[0] = (Fp::from(1u64), Fp::from(1u64));
        assert!(
            prover
                .prove::<BaseSponge, ScalarSponge>(
                    digest,
                    (Fp::from(42u64), invalid_point),
                    true,
                )
                .is_err()
        );

        let mut invalid_branch = witness;
        invalid_branch.proofs_verified = 1;
        assert!(
            prover
                .prove::<BaseSponge, ScalarSponge>(
                    digest,
                    (Fp::from(42u64), invalid_branch),
                    true,
                )
                .is_err()
        );
    }
}
