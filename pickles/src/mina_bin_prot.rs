//! Minimal Mina bin_prot codec required by
//! `Side_loaded_verification_key.Stable.V2`.

use ark_ff::{BigInteger, PrimeField};
use mina_curves::pasta::{Fp, Fq, Pallas};

use crate::composition_types::ProofsVerified;

pub const VERIFICATION_KEY_VERSION: u8 = 0x1b;
const POINTS: usize = 28;
const FIELD_BYTES: usize = 32;
const PAYLOAD_BYTES: usize = 2 + 2 * POINTS * FIELD_BYTES + 2;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SideLoadedVerificationKeyV2 {
    pub max_proofs_verified: ProofsVerified,
    pub actual_wrap_domain_size: ProofsVerified,
    pub commitments: Vec<(Fp, Fp)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinProtError {
    Base58,
    WrongLength(usize),
    InvalidProofsVerified(u8),
    InvalidVectorTerminator(usize),
    NonCanonicalField(usize),
    InvalidCurvePoint(usize),
}

fn encode_field(field: Fp, out: &mut Vec<u8>) {
    let mut bytes = field.into_bigint().to_bytes_le();
    bytes.resize(FIELD_BYTES, 0);
    out.extend(bytes);
}

fn decode_field(bytes: &[u8], index: usize) -> Result<Fp, BinProtError> {
    let bits = bytes
        .iter()
        .flat_map(|byte| (0..8).map(move |bit| byte & (1 << bit) != 0))
        .collect::<Vec<_>>();
    Fp::from_bigint(<Fp as PrimeField>::BigInt::from_bits_le(&bits))
        .ok_or(BinProtError::NonCanonicalField(index))
}

fn encode_proofs_verified(value: ProofsVerified) -> u8 {
    value.to_usize() as u8
}

fn decode_proofs_verified(value: u8) -> Result<ProofsVerified, BinProtError> {
    match value {
        0 => Ok(ProofsVerified::N0),
        1 => Ok(ProofsVerified::N1),
        2 => Ok(ProofsVerified::N2),
        value => Err(BinProtError::InvalidProofsVerified(value)),
    }
}

impl SideLoadedVerificationKeyV2 {
    pub fn to_bin_prot(&self) -> Result<Vec<u8>, BinProtError> {
        if self.commitments.len() != POINTS {
            return Err(BinProtError::WrongLength(self.commitments.len()));
        }
        let mut out = Vec::with_capacity(PAYLOAD_BYTES);
        out.push(encode_proofs_verified(self.max_proofs_verified));
        out.push(encode_proofs_verified(self.actual_wrap_domain_size));
        for (index, &(x, y)) in self.commitments.iter().enumerate() {
            let point = Pallas::new_unchecked(x, y);
            if !point.is_on_curve() || !point.is_in_correct_subgroup_assuming_on_curve() {
                return Err(BinProtError::InvalidCurvePoint(index));
            }
            encode_field(x, &mut out);
            encode_field(y, &mut out);
            if index == 6 || index == 21 {
                out.push(0); // bin_prot unit terminating each fixed Vector.
            }
        }
        Ok(out)
    }

    pub fn from_bin_prot(bytes: &[u8]) -> Result<Self, BinProtError> {
        if bytes.len() != PAYLOAD_BYTES {
            return Err(BinProtError::WrongLength(bytes.len()));
        }
        let max_proofs_verified = decode_proofs_verified(bytes[0])?;
        let actual_wrap_domain_size = decode_proofs_verified(bytes[1])?;
        let mut offset = 2;
        let mut commitments = Vec::with_capacity(POINTS);
        for index in 0..POINTS {
            let x = decode_field(&bytes[offset..offset + FIELD_BYTES], 2 * index)?;
            offset += FIELD_BYTES;
            let y = decode_field(&bytes[offset..offset + FIELD_BYTES], 2 * index + 1)?;
            offset += FIELD_BYTES;
            let point = Pallas::new_unchecked(x, y);
            if !point.is_on_curve() || !point.is_in_correct_subgroup_assuming_on_curve() {
                return Err(BinProtError::InvalidCurvePoint(index));
            }
            commitments.push((x, y));
            if index == 6 || index == 21 {
                if bytes[offset] != 0 {
                    return Err(BinProtError::InvalidVectorTerminator(offset));
                }
                offset += 1;
            }
        }
        Ok(Self {
            max_proofs_verified,
            actual_wrap_domain_size,
            commitments,
        })
    }

    pub fn to_base58_check(&self) -> Result<String, BinProtError> {
        Ok(mina_base58::encode(
            VERIFICATION_KEY_VERSION,
            &self.to_bin_prot()?,
        ))
    }

    pub fn from_base58_check(value: &str) -> Result<Self, BinProtError> {
        let payload = mina_base58::decode_version(value, VERIFICATION_KEY_VERSION)
            .map_err(|_| BinProtError::Base58)?;
        Self::from_bin_prot(&payload)
    }
}

#[cfg(test)]
mod tests {
    use ark_ec::{AffineRepr, CurveGroup};
    use sha2::{Digest, Sha256};

    use super::*;

    fn key() -> SideLoadedVerificationKeyV2 {
        let commitments = (1..=POINTS)
            .map(|scalar| {
                let point = (Pallas::generator() * Fq::from(scalar as u64)).into_affine();
                (point.x, point.y)
            })
            .collect();
        SideLoadedVerificationKeyV2 {
            max_proofs_verified: ProofsVerified::N2,
            actual_wrap_domain_size: ProofsVerified::N1,
            commitments,
        }
    }

    #[test]
    fn stable_v2_round_trips_bin_prot_and_base58() {
        let key = key();
        let bytes = key.to_bin_prot().unwrap();
        assert_eq!(bytes.len(), PAYLOAD_BYTES);
        assert_eq!(bytes[0..2], [2, 1]);
        assert_eq!(bytes[2 + 7 * 64], 0);
        assert_eq!(bytes[2 + 7 * 64 + 1 + 15 * 64], 0);
        assert_eq!(SideLoadedVerificationKeyV2::from_bin_prot(&bytes).unwrap(), key);
        let base58 = key.to_base58_check().unwrap();
        assert_eq!(
            SideLoadedVerificationKeyV2::from_base58_check(&base58).unwrap(),
            key
        );
    }

    #[test]
    fn stable_v2_rejects_bad_vector_terminator() {
        let mut bytes = key().to_bin_prot().unwrap();
        bytes[2 + 7 * 64] = 1;
        assert!(matches!(
            SideLoadedVerificationKeyV2::from_bin_prot(&bytes),
            Err(BinProtError::InvalidVectorTerminator(_))
        ));
    }

    /// MinaProtocol/mina
    /// `pickles/test/test_encoding_regression.ml`, commit
    /// 6f65312c4caebc3cb0ef25f74ba7ea641c91b033.
    #[test]
    fn stable_v2_matches_mina_dummy_base58_vector() {
        // OCaml Backend.Tock.Curve.one uses the opposite affine y-sign from
        // arkworks' `Pallas::generator()`.
        let generator = (
            Fp::from(1u64),
            "12418654782883325593414442427049395787963493412651469444558597405572177144507"
                .parse::<Fp>()
                .unwrap(),
        );
        let key = SideLoadedVerificationKeyV2 {
            max_proofs_verified: ProofsVerified::N2,
            actual_wrap_domain_size: ProofsVerified::N2,
            commitments: vec![generator; POINTS],
        };
        let encoded = key.to_base58_check().unwrap();
        assert_eq!(encoded.len(), 2459);
        assert_eq!(
            format!("{:x}", Sha256::digest(encoded.as_bytes())),
            "b5f98af721187a8a9ac83f060638dffbeb1bdeace644e1c6115c15649ace2621"
        );
    }
}
