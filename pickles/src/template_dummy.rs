//! Embedded compile-time dummy artifacts (OCaml `Pickles.Dummy` parity).
//!
//! OCaml `Pickles.compile` never proves: the proof-shaped values that seed
//! compilation are precomputed constants shipped with the source
//! (`Pickles.Dummy`, `Dummy.Ipa.Step/Wrap`). The recorded-program pipeline
//! used to manufacture the same values live — a template base cycle proof and
//! a bootstrap width-2 step proof — on every `compile`, which is pure
//! overhead (~4.5s native, ~7s wasm). This module embeds those artifacts,
//! generated once by `cargo test -p pickles --release --test recorded
//! generate_template_dummy_blob -- --ignored`, as a committed blob.
//!
//! The values never reach a circuit constant (the compiled circuits and the
//! verification key are byte-identical with or without the blob); they only
//! have to be VALID proofs of the fixed template/bootstrap circuits. A guard
//! test recompiles the template circuits and fails when they drift from the
//! blob, which is the signal to regenerate it.

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use kimchi::{
    circuits::{
        constraints::FeatureFlags,
        lookup::lookups::{LookupFeatures, LookupPatterns},
    },
    curve::KimchiCurve,
    verifier_index::VerifierIndex,
};
use mina_curves::pasta::{Fp, Fq, Pallas, Vesta};
use poly_commitment::{ipa::OpeningProof as IpaProof, ipa::SRS};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

use crate::common::FULL_ROUNDS;
use crate::mina_bin_prot::{
    StepMessagesForNextProofV1, WrapMessagesForNextWrapProofV1, WrapStatementMinimalV1,
};

/// Bump when the blob layout or the template/bootstrap circuits change.
const VERSION: u32 = 1;

/// The committed blob (empty until generated; an empty or stale blob simply
/// falls back to live proving).
static BLOB: &[u8] = include_bytes!("template_dummy.blob");

type PallasProof = kimchi::proof::ProverProof<Pallas, IpaProof<Pallas, FULL_ROUNDS>, FULL_ROUNDS>;
type VestaProof = kimchi::proof::ProverProof<Vesta, IpaProof<Vesta, FULL_ROUNDS>, FULL_ROUNDS>;
type VestaVi = VerifierIndex<FULL_ROUNDS, Vesta, SRS<Vesta>>;
type PallasVi = VerifierIndex<FULL_ROUNDS, Pallas, SRS<Pallas>>;

/// The concrete pieces of the template `BaseCaseProof` and the bootstrap
/// `RecursiveStepWidth2Proof`; `recorded.rs` (which owns the generic types)
/// assembles and disassembles them.
pub struct DummyParts {
    pub template_statement: Vec<Fq>,
    pub template_stable: WrapStatementMinimalV1,
    pub template_proof: PallasProof,
    pub template_step_proof: VestaProof,
    pub template_step_vi: VestaVi,
    pub template_wrap_vi: PallasVi,
    pub template_wrap_vk_pts: Vec<(Fp, Fp)>,
    pub boot_statement: Vec<Fp>,
    pub boot_proof: VestaProof,
    pub boot_vi: VestaVi,
    pub boot_vk_pts: Vec<(Fp, Fp)>,
    pub boot_m4n: StepMessagesForNextProofV1,
}

#[derive(Serialize, Deserialize)]
struct M4nStepDto {
    cpcs: Vec<u8>,
    old_bp: Vec<Vec<u8>>,
}

#[derive(Serialize, Deserialize)]
struct StableDto {
    flattened: Vec<u8>,
    m4nwrap_cpc: Vec<u8>,
    m4nwrap_old_bp: Vec<Vec<u8>>,
    m4nstep: M4nStepDto,
}

#[derive(Serialize, Deserialize)]
struct BlobDto {
    version: u32,
    template_statement: Vec<u8>,
    template_stable: StableDto,
    template_proof: Vec<u8>,
    template_step_proof: Vec<u8>,
    template_step_vi: Vec<u8>,
    template_wrap_vi: Vec<u8>,
    template_wrap_vk_pts: Vec<u8>,
    boot_statement: Vec<u8>,
    boot_proof: Vec<u8>,
    boot_vi: Vec<u8>,
    boot_vk_pts: Vec<u8>,
    boot_m4n: M4nStepDto,
}

fn fields_to_bytes<F: CanonicalSerialize>(xs: &[F]) -> Vec<u8> {
    let mut out = Vec::new();
    for x in xs {
        x.serialize_uncompressed(&mut out)
            .expect("field serialization is infallible for Vec sinks");
    }
    out
}

fn fields_from_bytes<F: CanonicalDeserialize + CanonicalSerialize + Default>(
    bytes: &[u8],
) -> Option<Vec<F>> {
    let size = F::default().uncompressed_size();
    if size == 0 || bytes.len() % size != 0 {
        return None;
    }
    bytes
        .chunks_exact(size)
        .map(|chunk| F::deserialize_uncompressed_unchecked(chunk).ok())
        .collect()
}

fn pairs_to_bytes<F: CanonicalSerialize + Copy>(xs: &[(F, F)]) -> Vec<u8> {
    let flat: Vec<F> = xs.iter().flat_map(|&(a, b)| [a, b]).collect();
    fields_to_bytes(&flat)
}

fn pairs_from_bytes<F: CanonicalDeserialize + CanonicalSerialize + Default + Copy>(
    bytes: &[u8],
) -> Option<Vec<(F, F)>> {
    let flat = fields_from_bytes::<F>(bytes)?;
    if flat.len() % 2 != 0 {
        return None;
    }
    Some(flat.chunks_exact(2).map(|p| (p[0], p[1])).collect())
}

fn m4n_to_dto(m: &StepMessagesForNextProofV1) -> M4nStepDto {
    M4nStepDto {
        cpcs: pairs_to_bytes(&m.challenge_polynomial_commitments),
        old_bp: m
            .old_bulletproof_challenges
            .iter()
            .map(|v| fields_to_bytes(v))
            .collect(),
    }
}

fn m4n_from_dto(dto: &M4nStepDto) -> Option<StepMessagesForNextProofV1> {
    Some(StepMessagesForNextProofV1 {
        challenge_polynomial_commitments: pairs_from_bytes(&dto.cpcs)?,
        old_bulletproof_challenges: dto
            .old_bp
            .iter()
            .map(|v| fields_from_bytes(v))
            .collect::<Option<Vec<_>>>()?,
    })
}

/// Rebuilds the `#[serde(skip)]` fields of a deserialized verifier index:
/// SRS handle, endo scalar, and the linearization (derived from the presence
/// of the optional-gate commitments, which the serialization does carry).
/// The `OnceLock` fields self-heal through their `get_or_init` accessors.
fn fixup_vi<G>(vi: &mut VerifierIndex<FULL_ROUNDS, G, SRS<G>>, srs: Arc<SRS<G>>)
where
    G: KimchiCurve<FULL_ROUNDS>,
{
    vi.srs = srs;
    vi.endo = *G::other_curve_endo();
    let patterns = match &vi.lookup_index {
        Some(li) => li.lookup_info.features.patterns,
        None => LookupPatterns {
            xor: false,
            lookup: false,
            range_check: false,
            foreign_field_mul: false,
        },
    };
    let feature_flags = FeatureFlags {
        range_check0: vi.range_check0_comm.is_some(),
        range_check1: vi.range_check1_comm.is_some(),
        foreign_field_add: vi.foreign_field_add_comm.is_some(),
        foreign_field_mul: vi.foreign_field_mul_comm.is_some(),
        xor: vi.xor_comm.is_some(),
        rot: vi.rot_comm.is_some(),
        lookup_features: LookupFeatures {
            patterns,
            joint_lookup_used: vi
                .lookup_index
                .as_ref()
                .map(|li| li.lookup_info.features.joint_lookup_used)
                .unwrap_or(false),
            uses_runtime_tables: vi
                .lookup_index
                .as_ref()
                .map(|li| li.lookup_info.features.uses_runtime_tables)
                .unwrap_or(false),
        },
    };
    let (linearization, powers_of_alpha) =
        kimchi::linearization::expr_linearization(Some(&feature_flags), true);
    vi.linearization = linearization;
    vi.powers_of_alpha = powers_of_alpha;
}

/// Encodes the parts into the blob byte format.
pub fn encode(parts: &DummyParts) -> Vec<u8> {
    let dto = BlobDto {
        version: VERSION,
        template_statement: fields_to_bytes(&parts.template_statement),
        template_stable: StableDto {
            flattened: fields_to_bytes(&parts.template_stable.flattened),
            m4nwrap_cpc: pairs_to_bytes(&[parts
                .template_stable
                .messages_for_next_wrap_proof
                .challenge_polynomial_commitment]),
            m4nwrap_old_bp: parts
                .template_stable
                .messages_for_next_wrap_proof
                .old_bulletproof_challenges
                .iter()
                .map(|v| fields_to_bytes(v))
                .collect(),
            m4nstep: m4n_to_dto(&parts.template_stable.messages_for_next_step_proof),
        },
        template_proof: rmp_serde::to_vec(&parts.template_proof).expect("proof serde"),
        template_step_proof: rmp_serde::to_vec(&parts.template_step_proof).expect("proof serde"),
        template_step_vi: rmp_serde::to_vec(&parts.template_step_vi).expect("vi serde"),
        template_wrap_vi: rmp_serde::to_vec(&parts.template_wrap_vi).expect("vi serde"),
        template_wrap_vk_pts: pairs_to_bytes(&parts.template_wrap_vk_pts),
        boot_statement: fields_to_bytes(&parts.boot_statement),
        boot_proof: rmp_serde::to_vec(&parts.boot_proof).expect("proof serde"),
        boot_vi: rmp_serde::to_vec(&parts.boot_vi).expect("vi serde"),
        boot_vk_pts: pairs_to_bytes(&parts.boot_vk_pts),
        boot_m4n: m4n_to_dto(&parts.boot_m4n),
    };
    rmp_serde::to_vec(&dto).expect("blob serde")
}

/// Decodes the embedded blob. Returns `None` (→ live proving fallback) when
/// the blob is absent, stale, or malformed.
pub fn decode_embedded() -> Option<DummyParts> {
    decode(BLOB)
}

fn decode(bytes: &[u8]) -> Option<DummyParts> {
    if bytes.is_empty() {
        return None;
    }
    let dto: BlobDto = rmp_serde::from_slice(bytes).ok()?;
    if dto.version != VERSION {
        return None;
    }
    let tick = crate::common::tick_srs(1 << crate::common::TICK_ROUNDS);
    let tock = crate::common::tock_srs(1 << crate::common::TOCK_ROUNDS);
    let mut template_step_vi: VestaVi = rmp_serde::from_slice(&dto.template_step_vi).ok()?;
    fixup_vi(&mut template_step_vi, tick.clone());
    let mut template_wrap_vi: PallasVi = rmp_serde::from_slice(&dto.template_wrap_vi).ok()?;
    fixup_vi(&mut template_wrap_vi, tock);
    let mut boot_vi: VestaVi = rmp_serde::from_slice(&dto.boot_vi).ok()?;
    fixup_vi(&mut boot_vi, tick);
    let m4nwrap_cpc = pairs_from_bytes::<Fq>(&dto.template_stable.m4nwrap_cpc)?;
    Some(DummyParts {
        template_statement: fields_from_bytes(&dto.template_statement)?,
        template_stable: WrapStatementMinimalV1 {
            flattened: fields_from_bytes(&dto.template_stable.flattened)?,
            messages_for_next_wrap_proof: WrapMessagesForNextWrapProofV1 {
                challenge_polynomial_commitment: *m4nwrap_cpc.first()?,
                old_bulletproof_challenges: dto
                    .template_stable
                    .m4nwrap_old_bp
                    .iter()
                    .map(|v| fields_from_bytes(v))
                    .collect::<Option<Vec<_>>>()?,
            },
            messages_for_next_step_proof: m4n_from_dto(&dto.template_stable.m4nstep)?,
        },
        template_proof: rmp_serde::from_slice(&dto.template_proof).ok()?,
        template_step_proof: rmp_serde::from_slice(&dto.template_step_proof).ok()?,
        template_step_vi,
        template_wrap_vi,
        template_wrap_vk_pts: pairs_from_bytes(&dto.template_wrap_vk_pts)?,
        boot_statement: fields_from_bytes(&dto.boot_statement)?,
        boot_proof: rmp_serde::from_slice(&dto.boot_proof).ok()?,
        boot_vi,
        boot_vk_pts: pairs_from_bytes(&dto.boot_vk_pts)?,
        boot_m4n: m4n_from_dto(&dto.boot_m4n)?,
    })
}
