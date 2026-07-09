//! Minimal Mina bin_prot codec required by
//! `Side_loaded_verification_key.Stable.V2`.

use ark_ff::{BigInteger, PrimeField};
use kimchi::{
    circuits::wires::{COLUMNS, PERMUTS},
    proof::{PointEvaluations, ProofEvaluations, ProverCommitments, ProverProof},
};
use mina_curves::pasta::{Fp, Fq, Pallas, Vesta};
use poly_commitment::{commitment::PolyComm, ipa::OpeningProof as IpaProof};

use crate::{common::FULL_ROUNDS, composition_types::ProofsVerified};

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

/// Mina `Wrap_wire_proof.Stable.V1` specialized to the Pallas/Tock wrap proof.
///
/// The layout follows `src/lib/crypto/pickles/wrap_wire_proof.ml`:
/// commitments, evaluations, `ft_eval1`, then the IPA bulletproof. The fixed
/// Mina vectors are encoded in their bin_prot order with a trailing unit byte.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WrapWireProofV1 {
    pub w_comm: [(Fp, Fp); COLUMNS],
    pub z_comm: (Fp, Fp),
    pub t_comm: [(Fp, Fp); 7],
    pub w: [(Fq, Fq); COLUMNS],
    pub coefficients: [(Fq, Fq); COLUMNS],
    pub z: (Fq, Fq),
    pub s: [(Fq, Fq); PERMUTS - 1],
    pub generic_selector: (Fq, Fq),
    pub poseidon_selector: (Fq, Fq),
    pub complete_add_selector: (Fq, Fq),
    pub mul_selector: (Fq, Fq),
    pub emul_selector: (Fq, Fq),
    pub endomul_scalar_selector: (Fq, Fq),
    pub ft_eval1: Fq,
    pub bulletproof_lr: Vec<((Fp, Fp), (Fp, Fp))>,
    pub z_1: Fq,
    pub z_2: Fq,
    pub delta: (Fp, Fp),
    pub challenge_polynomial_commitment: (Fp, Fp),
}

/// Rust representation of Mina
/// `Proof.Base.Wrap.Stable.V3`.
///
/// This starts the full Stable.V3 port at the exact wrapper boundary used by
/// Mina: the minimal wrap statement, the previous step proof evaluations, and
/// the stable wrap wire proof. The nested statement/message types are still
/// represented by their field elements, but `prev_evals` is kept structurally
/// so the `ArrayN16` bounds from Mina's `All_evals.Stable.V2` are enforced.
#[derive(Clone, Debug, PartialEq)]
pub struct WrapProofBaseV3 {
    pub statement: Vec<Fq>,
    pub prev_evals: WrapProofPrevEvalsV2,
    pub proof: WrapWireProofV1,
}

#[derive(Clone, Debug, PartialEq)]
pub struct WrapProofPrevEvalsV2 {
    pub ft_eval1: Fp,
    pub evals: ProofEvaluations<PointEvaluations<Vec<Fp>>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinProtError {
    Base58,
    WrongLength(usize),
    UnexpectedTrailingBytes(usize),
    InvalidProofsVerified(u8),
    InvalidVectorTerminator(usize),
    VectorTooLong { max: usize, actual: usize },
    WrongVectorLength { expected: usize, actual: usize },
    EmptyStatement,
    BoundedArrayTooLong { max: usize, actual: usize },
    UnsupportedLookupCommitments,
    UnsupportedOptionalEvaluation(&'static str),
    NonCanonicalField(usize),
    InvalidCurvePoint(usize),
}

fn encode_field(field: Fp, out: &mut Vec<u8>) {
    let mut bytes = field.into_bigint().to_bytes_le();
    bytes.resize(FIELD_BYTES, 0);
    out.extend(bytes);
}

fn encode_scalar(field: Fq, out: &mut Vec<u8>) {
    let mut bytes = field.into_bigint().to_bytes_le();
    bytes.resize(FIELD_BYTES, 0);
    out.extend(bytes);
}

fn decode_prime_field<F: PrimeField>(bytes: &[u8], index: usize) -> Result<F, BinProtError> {
    let bits = bytes
        .iter()
        .flat_map(|byte| (0..8).map(move |bit| byte & (1 << bit) != 0))
        .collect::<Vec<_>>();
    F::from_bigint(<F as PrimeField>::BigInt::from_bits_le(&bits))
        .ok_or(BinProtError::NonCanonicalField(index))
}

fn decode_field(bytes: &[u8], index: usize) -> Result<Fp, BinProtError> {
    decode_prime_field(bytes, index)
}

fn decode_scalar(bytes: &[u8], index: usize) -> Result<Fq, BinProtError> {
    decode_prime_field(bytes, index)
}

fn encode_point(point: (Fp, Fp), out: &mut Vec<u8>) -> Result<(), BinProtError> {
    validate_point(point, 0)?;
    encode_field(point.0, out);
    encode_field(point.1, out);
    Ok(())
}

fn validate_point(point: (Fp, Fp), index: usize) -> Result<(), BinProtError> {
    let point = Pallas::new_unchecked(point.0, point.1);
    if !point.is_on_curve() || !point.is_in_correct_subgroup_assuming_on_curve() {
        return Err(BinProtError::InvalidCurvePoint(index));
    }
    Ok(())
}

fn encode_field_pair(pair: (Fq, Fq), out: &mut Vec<u8>) {
    encode_scalar(pair.0, out);
    encode_scalar(pair.1, out);
}

fn decode_u8_len(bytes: &[u8], offset: &mut usize, max: usize) -> Result<usize, BinProtError> {
    if *offset >= bytes.len() {
        return Err(BinProtError::WrongLength(*offset));
    }
    let len = bytes[*offset] as usize;
    *offset += 1;
    if len > max {
        return Err(BinProtError::VectorTooLong { max, actual: len });
    }
    Ok(len)
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

impl WrapWireProofV1 {
    pub fn from_prover_proof(
        proof: &ProverProof<Pallas, IpaProof<Pallas, FULL_ROUNDS>, FULL_ROUNDS>,
    ) -> Result<Self, BinProtError> {
        if proof.commitments.lookup.is_some() {
            return Err(BinProtError::UnsupportedLookupCommitments);
        }
        let point = |p: &Pallas| -> (Fp, Fp) { (p.x, p.y) };
        let one_point = |commitment: &PolyComm<Pallas>| -> Result<(Fp, Fp), BinProtError> {
            if commitment.chunks.len() != 1 {
                return Err(BinProtError::WrongVectorLength {
                    expected: 1,
                    actual: commitment.chunks.len(),
                });
            }
            Ok(point(&commitment.chunks[0]))
        };
        let w_comm = proof
            .commitments
            .w_comm
            .iter()
            .map(one_point)
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .map_err(|values: Vec<_>| BinProtError::WrongVectorLength {
                expected: COLUMNS,
                actual: values.len(),
            })?;
        if proof.commitments.z_comm.chunks.len() != 1 {
            return Err(BinProtError::WrongVectorLength {
                expected: 1,
                actual: proof.commitments.z_comm.chunks.len(),
            });
        }
        if proof.commitments.t_comm.chunks.len() != 7 {
            return Err(BinProtError::WrongVectorLength {
                expected: 7,
                actual: proof.commitments.t_comm.chunks.len(),
            });
        }
        let z_comm = point(&proof.commitments.z_comm.chunks[0]);
        let t_comm = proof
            .commitments
            .t_comm
            .chunks
            .iter()
            .map(point)
            .collect::<Vec<_>>()
            .try_into()
            .map_err(|values: Vec<_>| BinProtError::WrongVectorLength {
                expected: 7,
                actual: values.len(),
            })?;

        let eval_pair = |name: &'static str,
                         eval: &PointEvaluations<Vec<Fq>>|
         -> Result<(Fq, Fq), BinProtError> {
            if eval.zeta.len() != 1 {
                return Err(BinProtError::WrongVectorLength {
                    expected: 1,
                    actual: eval.zeta.len(),
                });
            }
            if eval.zeta_omega.len() != 1 {
                return Err(BinProtError::WrongVectorLength {
                    expected: 1,
                    actual: eval.zeta_omega.len(),
                });
            }
            let _ = name;
            Ok((eval.zeta[0], eval.zeta_omega[0]))
        };
        let reject_optional = |name, value: &Option<PointEvaluations<Vec<Fq>>>| {
            if value.is_some() {
                Err(BinProtError::UnsupportedOptionalEvaluation(name))
            } else {
                Ok(())
            }
        };
        reject_optional("range_check0_selector", &proof.evals.range_check0_selector)?;
        reject_optional("range_check1_selector", &proof.evals.range_check1_selector)?;
        reject_optional("foreign_field_add_selector", &proof.evals.foreign_field_add_selector)?;
        reject_optional("foreign_field_mul_selector", &proof.evals.foreign_field_mul_selector)?;
        reject_optional("xor_selector", &proof.evals.xor_selector)?;
        reject_optional("rot_selector", &proof.evals.rot_selector)?;
        reject_optional("lookup_aggregation", &proof.evals.lookup_aggregation)?;
        reject_optional("lookup_table", &proof.evals.lookup_table)?;
        reject_optional("runtime_lookup_table", &proof.evals.runtime_lookup_table)?;
        reject_optional(
            "runtime_lookup_table_selector",
            &proof.evals.runtime_lookup_table_selector,
        )?;
        reject_optional("xor_lookup_selector", &proof.evals.xor_lookup_selector)?;
        reject_optional(
            "lookup_gate_lookup_selector",
            &proof.evals.lookup_gate_lookup_selector,
        )?;
        reject_optional(
            "range_check_lookup_selector",
            &proof.evals.range_check_lookup_selector,
        )?;
        reject_optional(
            "foreign_field_mul_lookup_selector",
            &proof.evals.foreign_field_mul_lookup_selector,
        )?;
        for value in &proof.evals.lookup_sorted {
            reject_optional("lookup_sorted", value)?;
        }

        Ok(Self {
            w_comm,
            z_comm,
            t_comm,
            w: proof
                .evals
                .w
                .iter()
                .map(|eval| eval_pair("w", eval))
                .collect::<Result<Vec<_>, _>>()?
                .try_into()
                .unwrap_or_else(|_| unreachable!("kimchi has 15 witness columns")),
            coefficients: proof
                .evals
                .coefficients
                .iter()
                .map(|eval| eval_pair("coefficients", eval))
                .collect::<Result<Vec<_>, _>>()?
                .try_into()
                .unwrap_or_else(|_| unreachable!("kimchi has 15 coefficient columns")),
            z: eval_pair("z", &proof.evals.z)?,
            s: proof
                .evals
                .s
                .iter()
                .map(|eval| eval_pair("s", eval))
                .collect::<Result<Vec<_>, _>>()?
                .try_into()
                .unwrap_or_else(|_| unreachable!("kimchi has 6 permutation columns")),
            generic_selector: eval_pair("generic_selector", &proof.evals.generic_selector)?,
            poseidon_selector: eval_pair("poseidon_selector", &proof.evals.poseidon_selector)?,
            complete_add_selector: eval_pair(
                "complete_add_selector",
                &proof.evals.complete_add_selector,
            )?,
            mul_selector: eval_pair("mul_selector", &proof.evals.mul_selector)?,
            emul_selector: eval_pair("emul_selector", &proof.evals.emul_selector)?,
            endomul_scalar_selector: eval_pair(
                "endomul_scalar_selector",
                &proof.evals.endomul_scalar_selector,
            )?,
            ft_eval1: proof.ft_eval1,
            bulletproof_lr: proof
                .proof
                .lr
                .iter()
                .map(|(l, r)| (point(l), point(r)))
                .collect(),
            z_1: proof.proof.z1,
            z_2: proof.proof.z2,
            delta: point(&proof.proof.delta),
            challenge_polynomial_commitment: point(&proof.proof.sg),
        })
    }

    pub fn to_prover_proof(
        &self,
    ) -> Result<ProverProof<Pallas, IpaProof<Pallas, FULL_ROUNDS>, FULL_ROUNDS>, BinProtError>
    {
        let point = |coords: (Fp, Fp), index: usize| -> Result<Pallas, BinProtError> {
            validate_point(coords, index)?;
            Ok(Pallas::new_unchecked(coords.0, coords.1))
        };
        let poly = |coords: (Fp, Fp), index| {
            Ok(PolyComm {
                chunks: vec![point(coords, index)?],
            })
        };
        let eval = |pair: (Fq, Fq)| PointEvaluations {
            zeta: vec![pair.0],
            zeta_omega: vec![pair.1],
        };
        let commitments = ProverCommitments {
            w_comm: self
                .w_comm
                .iter()
                .enumerate()
                .map(|(index, &coords)| poly(coords, index))
                .collect::<Result<Vec<_>, _>>()?
                .try_into()
                .unwrap_or_else(|_| unreachable!("wire proof has 15 witness commitments")),
            z_comm: poly(self.z_comm, COLUMNS)?,
            t_comm: PolyComm {
                chunks: self
                    .t_comm
                    .iter()
                    .enumerate()
                    .map(|(index, &coords)| point(coords, COLUMNS + 1 + index))
                    .collect::<Result<Vec<_>, _>>()?,
            },
            lookup: None,
        };
        let proof = IpaProof {
            lr: self
                .bulletproof_lr
                .iter()
                .enumerate()
                .map(|(index, &(l, r))| {
                    Ok((point(l, index * 2)?, point(r, index * 2 + 1)?))
                })
                .collect::<Result<Vec<_>, _>>()?,
            z1: self.z_1,
            z2: self.z_2,
            delta: point(self.delta, 0)?,
            sg: point(self.challenge_polynomial_commitment, 1)?,
        };
        let evals = ProofEvaluations {
            public: None,
            w: self.w.map(eval),
            z: eval(self.z),
            s: self.s.map(eval),
            coefficients: self.coefficients.map(eval),
            generic_selector: eval(self.generic_selector),
            poseidon_selector: eval(self.poseidon_selector),
            complete_add_selector: eval(self.complete_add_selector),
            mul_selector: eval(self.mul_selector),
            emul_selector: eval(self.emul_selector),
            endomul_scalar_selector: eval(self.endomul_scalar_selector),
            range_check0_selector: None,
            range_check1_selector: None,
            foreign_field_add_selector: None,
            foreign_field_mul_selector: None,
            xor_selector: None,
            rot_selector: None,
            lookup_aggregation: None,
            lookup_table: None,
            lookup_sorted: [None, None, None, None, None],
            runtime_lookup_table: None,
            runtime_lookup_table_selector: None,
            xor_lookup_selector: None,
            lookup_gate_lookup_selector: None,
            range_check_lookup_selector: None,
            foreign_field_mul_lookup_selector: None,
        };
        Ok(ProverProof {
            commitments,
            proof,
            evals,
            ft_eval1: self.ft_eval1,
            prev_challenges: Vec::new(),
        })
    }

    pub fn to_bin_prot(&self) -> Result<Vec<u8>, BinProtError> {
        if self.bulletproof_lr.len() > 16 {
            return Err(BinProtError::VectorTooLong {
                max: 16,
                actual: self.bulletproof_lr.len(),
            });
        }
        let mut out = Vec::new();
        for (index, &point) in self.w_comm.iter().enumerate() {
            validate_point(point, index)?;
            encode_point(point, &mut out)?;
        }
        out.push(0);
        encode_point(self.z_comm, &mut out)?;
        for (index, &point) in self.t_comm.iter().enumerate() {
            validate_point(point, COLUMNS + 1 + index)?;
            encode_point(point, &mut out)?;
        }
        out.push(0);
        for pair in self.w {
            encode_field_pair(pair, &mut out);
        }
        out.push(0);
        for pair in self.coefficients {
            encode_field_pair(pair, &mut out);
        }
        out.push(0);
        encode_field_pair(self.z, &mut out);
        for pair in self.s {
            encode_field_pair(pair, &mut out);
        }
        out.push(0);
        for pair in [
            self.generic_selector,
            self.poseidon_selector,
            self.complete_add_selector,
            self.mul_selector,
            self.emul_selector,
            self.endomul_scalar_selector,
        ] {
            encode_field_pair(pair, &mut out);
        }
        encode_scalar(self.ft_eval1, &mut out);
        out.push(self.bulletproof_lr.len() as u8);
        for &(left, right) in &self.bulletproof_lr {
            encode_point(left, &mut out)?;
            encode_point(right, &mut out)?;
        }
        encode_scalar(self.z_1, &mut out);
        encode_scalar(self.z_2, &mut out);
        encode_point(self.delta, &mut out)?;
        encode_point(self.challenge_polynomial_commitment, &mut out)?;
        Ok(out)
    }

    pub fn from_bin_prot(bytes: &[u8]) -> Result<Self, BinProtError> {
        let mut offset = 0usize;
        let mut field_index = 0usize;
        let mut scalar_index = 0usize;
        let read_field = |offset: &mut usize, field_index: &mut usize| {
            if *offset + FIELD_BYTES > bytes.len() {
                return Err(BinProtError::WrongLength(bytes.len()));
            }
            let value = decode_field(&bytes[*offset..*offset + FIELD_BYTES], *field_index)?;
            *offset += FIELD_BYTES;
            *field_index += 1;
            Ok(value)
        };
        let read_scalar = |offset: &mut usize, scalar_index: &mut usize| {
            if *offset + FIELD_BYTES > bytes.len() {
                return Err(BinProtError::WrongLength(bytes.len()));
            }
            let value = decode_scalar(&bytes[*offset..*offset + FIELD_BYTES], *scalar_index)?;
            *offset += FIELD_BYTES;
            *scalar_index += 1;
            Ok(value)
        };
        let read_point = |offset: &mut usize,
                          field_index: &mut usize,
                          point_index: usize|
         -> Result<(Fp, Fp), BinProtError> {
            let x = read_field(offset, field_index)?;
            let y = read_field(offset, field_index)?;
            validate_point((x, y), point_index)?;
            Ok((x, y))
        };
        let read_pair = |offset: &mut usize,
                         scalar_index: &mut usize|
         -> Result<(Fq, Fq), BinProtError> {
            Ok((
                read_scalar(offset, scalar_index)?,
                read_scalar(offset, scalar_index)?,
            ))
        };
        let read_unit = |offset: &mut usize| {
            if *offset >= bytes.len() {
                return Err(BinProtError::WrongLength(bytes.len()));
            }
            if bytes[*offset] != 0 {
                return Err(BinProtError::InvalidVectorTerminator(*offset));
            }
            *offset += 1;
            Ok(())
        };

        let mut w_comm = Vec::with_capacity(COLUMNS);
        for index in 0..COLUMNS {
            w_comm.push(read_point(&mut offset, &mut field_index, index)?);
        }
        read_unit(&mut offset)?;
        let z_comm = read_point(&mut offset, &mut field_index, COLUMNS)?;
        let mut t_comm = Vec::with_capacity(7);
        for index in 0..7 {
            t_comm.push(read_point(&mut offset, &mut field_index, COLUMNS + 1 + index)?);
        }
        read_unit(&mut offset)?;

        let mut w = Vec::with_capacity(COLUMNS);
        for _ in 0..COLUMNS {
            w.push(read_pair(&mut offset, &mut scalar_index)?);
        }
        read_unit(&mut offset)?;
        let mut coefficients = Vec::with_capacity(COLUMNS);
        for _ in 0..COLUMNS {
            coefficients.push(read_pair(&mut offset, &mut scalar_index)?);
        }
        read_unit(&mut offset)?;
        let z = read_pair(&mut offset, &mut scalar_index)?;
        let mut s = Vec::with_capacity(PERMUTS - 1);
        for _ in 0..PERMUTS - 1 {
            s.push(read_pair(&mut offset, &mut scalar_index)?);
        }
        read_unit(&mut offset)?;
        let generic_selector = read_pair(&mut offset, &mut scalar_index)?;
        let poseidon_selector = read_pair(&mut offset, &mut scalar_index)?;
        let complete_add_selector = read_pair(&mut offset, &mut scalar_index)?;
        let mul_selector = read_pair(&mut offset, &mut scalar_index)?;
        let emul_selector = read_pair(&mut offset, &mut scalar_index)?;
        let endomul_scalar_selector = read_pair(&mut offset, &mut scalar_index)?;
        let ft_eval1 = read_scalar(&mut offset, &mut scalar_index)?;
        let lr_len = decode_u8_len(bytes, &mut offset, 16)?;
        let mut bulletproof_lr = Vec::with_capacity(lr_len);
        for index in 0..lr_len {
            bulletproof_lr.push((
                read_point(&mut offset, &mut field_index, index * 2)?,
                read_point(&mut offset, &mut field_index, index * 2 + 1)?,
            ));
        }
        let z_1 = read_scalar(&mut offset, &mut scalar_index)?;
        let z_2 = read_scalar(&mut offset, &mut scalar_index)?;
        let delta = read_point(&mut offset, &mut field_index, 0)?;
        let challenge_polynomial_commitment = read_point(&mut offset, &mut field_index, 1)?;
        if offset != bytes.len() {
            return Err(BinProtError::UnexpectedTrailingBytes(bytes.len() - offset));
        }
        Ok(Self {
            w_comm: w_comm.try_into().unwrap(),
            z_comm,
            t_comm: t_comm.try_into().unwrap(),
            w: w.try_into().unwrap(),
            coefficients: coefficients.try_into().unwrap(),
            z,
            s: s.try_into().unwrap(),
            generic_selector,
            poseidon_selector,
            complete_add_selector,
            mul_selector,
            emul_selector,
            endomul_scalar_selector,
            ft_eval1,
            bulletproof_lr,
            z_1,
            z_2,
            delta,
            challenge_polynomial_commitment,
        })
    }
}

impl WrapProofPrevEvalsV2 {
    pub fn from_step_proof(
        proof: &ProverProof<Vesta, IpaProof<Vesta, FULL_ROUNDS>, FULL_ROUNDS>,
    ) -> Result<Self, BinProtError> {
        validate_prev_evals(&proof.evals)?;
        Ok(Self {
            ft_eval1: proof.ft_eval1,
            evals: proof.evals.clone(),
        })
    }
}

impl WrapProofBaseV3 {
    pub fn from_proofs(
        statement: Vec<Fq>,
        prev_step_proof: &ProverProof<Vesta, IpaProof<Vesta, FULL_ROUNDS>, FULL_ROUNDS>,
        wrap_proof: &ProverProof<Pallas, IpaProof<Pallas, FULL_ROUNDS>, FULL_ROUNDS>,
    ) -> Result<Self, BinProtError> {
        if statement.is_empty() {
            return Err(BinProtError::EmptyStatement);
        }
        Ok(Self {
            statement,
            prev_evals: WrapProofPrevEvalsV2::from_step_proof(prev_step_proof)?,
            proof: WrapWireProofV1::from_prover_proof(wrap_proof)?,
        })
    }
}

fn validate_prev_evals(
    evals: &ProofEvaluations<PointEvaluations<Vec<Fp>>>,
) -> Result<(), BinProtError> {
    fn validate_point_evals(evals: &PointEvaluations<Vec<Fp>>) -> Result<(), BinProtError> {
        for actual in [evals.zeta.len(), evals.zeta_omega.len()] {
            if actual > 16 {
                return Err(BinProtError::BoundedArrayTooLong { max: 16, actual });
            }
        }
        Ok(())
    }
    if let Some(public) = &evals.public {
        validate_point_evals(public)?;
    }
    for eval in &evals.w {
        validate_point_evals(eval)?;
    }
    validate_point_evals(&evals.z)?;
    for eval in &evals.s {
        validate_point_evals(eval)?;
    }
    for eval in &evals.coefficients {
        validate_point_evals(eval)?;
    }
    validate_point_evals(&evals.generic_selector)?;
    validate_point_evals(&evals.poseidon_selector)?;
    validate_point_evals(&evals.complete_add_selector)?;
    validate_point_evals(&evals.mul_selector)?;
    validate_point_evals(&evals.emul_selector)?;
    validate_point_evals(&evals.endomul_scalar_selector)?;
    for eval in [
        &evals.range_check0_selector,
        &evals.range_check1_selector,
        &evals.foreign_field_add_selector,
        &evals.foreign_field_mul_selector,
        &evals.xor_selector,
        &evals.rot_selector,
        &evals.lookup_aggregation,
        &evals.lookup_table,
        &evals.runtime_lookup_table,
        &evals.runtime_lookup_table_selector,
        &evals.xor_lookup_selector,
        &evals.lookup_gate_lookup_selector,
        &evals.range_check_lookup_selector,
        &evals.foreign_field_mul_lookup_selector,
    ] {
        if let Some(eval) = eval {
            validate_point_evals(eval)?;
        }
    }
    for eval in &evals.lookup_sorted {
        if let Some(eval) = eval {
            validate_point_evals(eval)?;
        }
    }
    Ok(())
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

    fn pallas_point(scalar: u64) -> (Fp, Fp) {
        let point = (Pallas::generator() * Fq::from(scalar)).into_affine();
        (point.x, point.y)
    }

    fn scalar_pair(seed: u64) -> (Fq, Fq) {
        (Fq::from(seed), Fq::from(seed + 10_000))
    }

    fn wrap_wire(lr_len: usize) -> WrapWireProofV1 {
        WrapWireProofV1 {
            w_comm: std::array::from_fn(|index| pallas_point(1 + index as u64)),
            z_comm: pallas_point(100),
            t_comm: std::array::from_fn(|index| pallas_point(200 + index as u64)),
            w: std::array::from_fn(|index| scalar_pair(300 + index as u64)),
            coefficients: std::array::from_fn(|index| scalar_pair(400 + index as u64)),
            z: scalar_pair(500),
            s: std::array::from_fn(|index| scalar_pair(600 + index as u64)),
            generic_selector: scalar_pair(700),
            poseidon_selector: scalar_pair(701),
            complete_add_selector: scalar_pair(702),
            mul_selector: scalar_pair(703),
            emul_selector: scalar_pair(704),
            endomul_scalar_selector: scalar_pair(705),
            ft_eval1: Fq::from(800u64),
            bulletproof_lr: (0..lr_len)
                .map(|index| {
                    (
                        pallas_point(900 + 2 * index as u64),
                        pallas_point(901 + 2 * index as u64),
                    )
                })
                .collect(),
            z_1: Fq::from(1_000u64),
            z_2: Fq::from(1_001u64),
            delta: pallas_point(1_100),
            challenge_polynomial_commitment: pallas_point(1_101),
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

    /// Rust-side regression fixture for the Mina
    /// `Wrap_wire_proof.Stable.V1` bin_prot layout. Mina upstream does not
    /// expose a Base58 proof fixture in `test_encoding_regression.ml`; this
    /// digest pins the exact byte order ported from `wrap_wire_proof.ml`.
    #[test]
    fn wrap_wire_proof_v1_has_stable_bin_prot_digest() {
        let bytes = wrap_wire(16).to_bin_prot().unwrap();
        assert_eq!(bytes.len(), 4_454 + 16 * 128);
        assert_eq!(
            format!("{:x}", Sha256::digest(&bytes)),
            "db308f97e363b683dc09342ecb2cbf4d9dc7f7e7fc17bf872fcbb60bf7af5ced"
        );
    }

    #[test]
    fn wrap_wire_proof_v1_round_trips_bin_prot_and_kimchi_shape() {
        let wire = wrap_wire(3);
        let bytes = wire.to_bin_prot().unwrap();
        assert_eq!(bytes.len(), 4_454 + 3 * 128);
        assert_eq!(bytes[15 * 64], 0);
        assert_eq!(bytes[15 * 64 + 1 + 64 + 7 * 64], 0);

        let decoded = WrapWireProofV1::from_bin_prot(&bytes).unwrap();
        assert_eq!(decoded, wire);

        let kimchi = decoded.to_prover_proof().unwrap();
        assert_eq!(kimchi.commitments.w_comm.len(), COLUMNS);
        assert_eq!(kimchi.commitments.t_comm.chunks.len(), 7);
        assert_eq!(kimchi.proof.lr.len(), 3);
        assert_eq!(WrapWireProofV1::from_prover_proof(&kimchi).unwrap(), wire);
    }

    #[test]
    fn wrap_wire_proof_v1_rejects_malleable_inputs() {
        let wire = wrap_wire(17);
        assert_eq!(
            wire.to_bin_prot().unwrap_err(),
            BinProtError::VectorTooLong {
                max: 16,
                actual: 17
            }
        );

        let mut bytes = wrap_wire(1).to_bin_prot().unwrap();
        bytes[15 * 64] = 1;
        assert!(matches!(
            WrapWireProofV1::from_bin_prot(&bytes),
            Err(BinProtError::InvalidVectorTerminator(_))
        ));

        let mut bytes = wrap_wire(1).to_bin_prot().unwrap();
        bytes.push(0);
        assert_eq!(
            WrapWireProofV1::from_bin_prot(&bytes).unwrap_err(),
            BinProtError::UnexpectedTrailingBytes(1)
        );
    }
}
