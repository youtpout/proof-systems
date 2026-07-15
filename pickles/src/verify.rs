//! Standalone out-of-circuit verification of Pickles wrap proofs.
//!
//! Port of `verify.ml` / `Side_loaded.verify`: checks a [`MinaWrapProof`]
//! against a side-loaded verification key alone — no prover backend, no
//! compiled wrap circuit. The kimchi verifier index is reconstructed from the
//! key's 28 commitments and its wrap domain, mirroring the structural fields
//! that `compile_to_indexes` produces for [`crate::api::WrapCircuit`] (no
//! optional gates, no lookups, zero prev challenges).

use ark_poly::EvaluationDomain;
use groupmap::GroupMap;
use kimchi::{
    circuits::{
        constraints::{FeatureFlags, ZK_ROWS_BY_DEFAULT},
        lookup::lookups::{LookupFeatures, LookupPatterns},
        polynomials::permutation::{permutation_vanishing_polynomial, zk_w, Shifts},
    },
    curve::KimchiCurve,
    verifier_index::VerifierIndex,
};
use mina_curves::pasta::{Fp, Fq, Pallas, Vesta};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi,
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use poly_commitment::{commitment::CommitmentCurve, ipa::SRS, SRS as _};

use crate::{
    api::MinaWrapProof,
    common::{FULL_ROUNDS, TICK_ROUNDS},
    recursive_step::embed_fp_to_fq,
    side_loaded::{SideLoadedStableV2Error, SideLoadedVerificationKey},
};

/// Slot of the messages-for-next-step-proof digest in
/// `Wrap.Statement.to_data` (after the deferred values, before the
/// bulletproof challenges).
pub const STATEMENT_DIGEST_SLOT: usize = 12;

type PallasBase =
    DefaultFqSponge<mina_curves::pasta::PallasParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type PallasScalar = DefaultFrSponge<Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

#[derive(Debug)]
pub enum StandaloneVerifyError {
    VerificationKey(SideLoadedStableV2Error),
    ProofDecoding,
    StatementTooShort(usize),
    /// One challenge vector is required per challenge-polynomial commitment.
    MalformedMessages,
    /// The statement's digest does not bind the claimed application state.
    AppStateMismatch,
    KimchiRejection(String),
}

/// Rebuilds the kimchi verifier index of a wrap circuit from a side-loaded
/// key. `public_input_size` is the wrap statement length (13 + step IPA
/// rounds + 9).
pub fn wrap_verifier_index_from_side_loaded(
    vk: &SideLoadedVerificationKey,
    public_input_size: usize,
) -> VerifierIndex<FULL_ROUNDS, Pallas, SRS<Pallas>> {
    let domain = ark_poly::Radix2EvaluationDomain::<Fq>::new(1 << vk.wrap_domain_log2)
        .expect("wrap domain size is a supported power of two");
    // Wrap proofs are made over the full Tock SRS (2^15) regardless of the
    // circuit's domain, so their IPA openings always have 15 rounds.
    let srs = crate::common::tock_srs(1 << crate::common::TOCK_ROUNDS);
    srs.get_lagrange_basis(domain);

    let comms = vk.commitments();
    let comm = |index: usize| poly_commitment::commitment::PolyComm {
        chunks: vec![Pallas::new_unchecked(comms[index].0, comms[index].1)],
    };

    // The wrap circuit uses no optional gates and no lookups.
    let feature_flags = FeatureFlags {
        range_check0: false,
        range_check1: false,
        foreign_field_add: false,
        foreign_field_mul: false,
        xor: false,
        rot: false,
        lookup_features: LookupFeatures {
            patterns: LookupPatterns {
                xor: false,
                lookup: false,
                range_check: false,
                foreign_field_mul: false,
            },
            joint_lookup_used: false,
            uses_runtime_tables: false,
        },
    };
    let (linearization, powers_of_alpha) =
        kimchi::linearization::expr_linearization(Some(&feature_flags), true);

    let zk_rows = ZK_ROWS_BY_DEFAULT;
    let shifts = Shifts::new(&domain);

    VerifierIndex {
        domain,
        max_poly_size: srs.max_poly_size(),
        zk_rows,
        srs,
        public: public_input_size,
        prev_challenges: 0,
        // Pickles canonical order: 7 sigma, 15 coefficients, then generic,
        // psm, complete_add, mul, emul, endomul_scalar.
        sigma_comm: core::array::from_fn(|i| comm(i)),
        coefficients_comm: core::array::from_fn(|i| comm(7 + i)),
        generic_comm: comm(22),
        psm_comm: comm(23),
        complete_add_comm: comm(24),
        mul_comm: comm(25),
        emul_comm: comm(26),
        endomul_scalar_comm: comm(27),
        range_check0_comm: None,
        range_check1_comm: None,
        foreign_field_add_comm: None,
        foreign_field_mul_comm: None,
        xor_comm: None,
        rot_comm: None,
        shift: *shifts.shifts(),
        permutation_vanishing_polynomial_m: {
            let cell = std::sync::OnceLock::new();
            cell.set(permutation_vanishing_polynomial(domain, zk_rows))
                .unwrap_or_else(|_| unreachable!("fresh OnceLock"));
            cell
        },
        w: {
            let cell = std::sync::OnceLock::new();
            cell.set(zk_w(domain, zk_rows))
                .unwrap_or_else(|_| unreachable!("fresh OnceLock"));
            cell
        },
        endo: *Pallas::other_curve_endo(),
        lookup_index: None,
        linearization,
        powers_of_alpha,
    }
}

/// Verifies the kimchi wrap proof of `proof` against a side-loaded key,
/// with the wrap statement as public input. Does not bind the statement to
/// any application state — see [`verify_side_loaded`].
pub fn verify_wrap_proof(
    vk: &SideLoadedVerificationKey,
    proof: &MinaWrapProof,
) -> Result<(), StandaloneVerifyError> {
    let prover_proof = crate::mina_bin_prot::WrapWireProofV1::from_bin_prot(&proof.wrap_wire_proof)
        .and_then(|wire| wire.to_prover_proof())
        .map_err(|_| StandaloneVerifyError::ProofDecoding)?;
    let index = wrap_verifier_index_from_side_loaded(vk, proof.statement.len());
    let group_map = <Pallas as CommitmentCurve>::Map::setup();
    kimchi::verifier::verify::<
        FULL_ROUNDS,
        Pallas,
        PallasBase,
        PallasScalar,
        poly_commitment::ipa::OpeningProof<Pallas, FULL_ROUNDS>,
    >(&group_map, &index, &prover_proof, &proof.statement)
    .map_err(|error| StandaloneVerifyError::KimchiRejection(format!("{error:?}")))
}

/// Verifies a Pickles wrap proof end to end against its embedded side-loaded
/// key: decodes the key, checks that the statement's
/// messages-for-next-step-proof digest binds the claimed application state
/// (together with the challenge-polynomial commitments and old bulletproof
/// challenges of the proofs it verified — empty for a base-case proof), and
/// runs the kimchi verifier. Returns the decoded key on success.
pub fn verify_side_loaded(
    app_state: &[Fp],
    challenge_polynomial_commitments: &[(Fp, Fp)],
    old_bulletproof_challenges: &[Vec<Fp>],
    proof: &MinaWrapProof,
) -> Result<SideLoadedVerificationKey, StandaloneVerifyError> {
    verify_side_loaded_with_step_vk(
        app_state,
        None,
        challenge_polynomial_commitments,
        old_bulletproof_challenges,
        proof,
    )
}

/// [`verify_side_loaded`] with an explicit `dlog_plonk_index`: the wrap
/// verification-key commitments hashed into the statement's
/// messages-for-next-step-proof digest. In a standard Pickles program all
/// branches share one wrap key and the digest binds the proof's own
/// side-loaded key (`None`); pass `Some` when the step proof committed to a
/// different wrap key than the one wrapping it.
pub fn verify_side_loaded_with_step_vk(
    app_state: &[Fp],
    dlog_plonk_index: Option<&[(Fp, Fp)]>,
    challenge_polynomial_commitments: &[(Fp, Fp)],
    old_bulletproof_challenges: &[Vec<Fp>],
    proof: &MinaWrapProof,
) -> Result<SideLoadedVerificationKey, StandaloneVerifyError> {
    if challenge_polynomial_commitments.len() != old_bulletproof_challenges.len() {
        return Err(StandaloneVerifyError::MalformedMessages);
    }
    let vk = SideLoadedVerificationKey::from_stable_v2_base58(
        TICK_ROUNDS as u8,
        &proof.side_loaded_verification_key,
    )
    .map_err(StandaloneVerifyError::VerificationKey)?;

    if proof.statement.len() <= STATEMENT_DIGEST_SLOT {
        return Err(StandaloneVerifyError::StatementTooShort(
            proof.statement.len(),
        ));
    }
    let digest = crate::hash_messages::hash_messages_for_next_step_proof_ref(
        Vesta::sponge_params(),
        dlog_plonk_index.unwrap_or_else(|| vk.commitments()),
        app_state,
        challenge_polynomial_commitments,
        old_bulletproof_challenges,
    );
    if proof.statement[STATEMENT_DIGEST_SLOT] != embed_fp_to_fq(digest) {
        return Err(StandaloneVerifyError::AppStateMismatch);
    }

    verify_wrap_proof(&vk, proof)?;
    Ok(vk)
}

/// [`verify_side_loaded`] for base-case (width 0) proofs, which carry no
/// previous accumulators in their messages.
pub fn verify_side_loaded_base_case(
    app_state: &[Fp],
    proof: &MinaWrapProof,
) -> Result<SideLoadedVerificationKey, StandaloneVerifyError> {
    verify_side_loaded(app_state, &[], &[], proof)
}
