use ark_serialize::CanonicalDeserialize;
use mina_curves::pasta::Fp;
use napi::bindgen_prelude::*;
use napi_derive::napi;
use pickles::{
    api::{BaseCaseRuleBackend, StepApp},
    composition_types::ProofsVerified,
    inductive_rule::{InductiveRule, RuleId},
};
use snarky::{loc, FieldVar, RunState, SnarkyResult};

const SQUARE_STEP_ROUNDS: usize = 16;
const SQUARE_STATEMENT_LEN: usize = 13 + SQUARE_STEP_ROUNDS + 11;

#[derive(Clone, Copy)]
struct SquareApp;

impl StepApp for SquareApp {
    type Witness = Fp;

    fn main(
        &self,
        sys: &mut RunState<Fp>,
        witness: Option<&Self::Witness>,
    ) -> SnarkyResult<Vec<FieldVar<Fp>>> {
        let x: FieldVar<Fp> = sys.compute(loc!(), |_| *witness.unwrap())?;
        Ok(vec![x.mul(&x, None, loc!(), sys)?])
    }

    fn state(&self, witness: &Self::Witness) -> Vec<Fp> {
        vec![*witness * *witness]
    }
}

fn parse_fp_decimal(value: &str, name: &str) -> Result<Fp> {
    value
        .parse::<Fp>()
        .map_err(|_| Error::from_reason(format!("{name}: expected decimal Pasta Fp field")))
}

fn parse_fp_bytes(bytes: &[u8], name: &str) -> Result<Vec<Fp>> {
    const FIELD_BYTES: usize = 32;
    if !bytes.len().is_multiple_of(FIELD_BYTES) {
        return Err(Error::from_reason(format!(
            "{name}: expected a multiple of {FIELD_BYTES} canonical Fp bytes"
        )));
    }
    bytes
        .chunks_exact(FIELD_BYTES)
        .map(|chunk| {
            Fp::deserialize_compressed(chunk)
                .map_err(|_| Error::from_reason(format!("{name}: non-canonical Pasta Fp encoding")))
        })
        .collect()
}

/// Proves a recorded circuit (the JSON envelope produced by o1js's
/// constraint-system adapter — see `pickles::recorded::RecordedCircuit`)
/// through the base-case Pickles pipeline, with the witness variable values
/// as decimal Fp strings. Returns `{ appState, proof }` where `proof` is the
/// o1js wrap proof JSON envelope.
#[napi(js_name = "rust_pickles_prove_recorded_base")]
pub fn rust_pickles_prove_recorded_base(
    circuit_json: String,
    witness_decimal: Vec<String>,
) -> Result<String> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    let witness = witness_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "witness"))
        .collect::<Result<Vec<_>>>()?;
    let proved = pickles::recorded::prove_recorded_base_case(circuit, witness)
        .map_err(|err| Error::from_reason(format!("rust pickles prove failed: {err:?}")))?;
    let envelope = serde_json::json!({
        "appState": proved
            .app_state
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        "proof": proved.proof.to_o1js_json_value(),
    });
    serde_json::to_string(&envelope)
        .map_err(|err| Error::from_reason(format!("envelope encoding failed: {err}")))
}

/// Verifies a Pickles wrap proof (the o1js JSON envelope produced by
/// `prove_with_mina_encoding` backends) against the side-loaded verification
/// key it embeds — no prover backend, no compiled circuit.
///
/// `app_state_decimal` is the claimed application state as decimal Fp strings.
/// `challenge_polynomial_commitments` / `old_bulletproof_challenges` are the
/// recursion messages of the proofs this one verified — empty arrays for a
/// base-case proof. Commitments are `[x, y]` decimal pairs; challenge vectors
/// are arrays of decimal Fp strings, one vector per commitment.
#[napi(js_name = "rust_pickles_verify_side_loaded")]
pub fn rust_pickles_verify_side_loaded(
    app_state_decimal: Vec<String>,
    challenge_polynomial_commitments: Vec<Vec<String>>,
    old_bulletproof_challenges: Vec<Vec<String>>,
    proof_json: String,
) -> Result<bool> {
    let app_state = app_state_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "app_state"))
        .collect::<Result<Vec<_>>>()?;
    let commitments = challenge_polynomial_commitments
        .iter()
        .map(|pair| {
            if pair.len() != 2 {
                return Err(Error::from_reason(
                    "challenge_polynomial_commitments: expected [x, y] decimal pairs".to_string(),
                ));
            }
            Ok((
                parse_fp_decimal(&pair[0], "commitment x")?,
                parse_fp_decimal(&pair[1], "commitment y")?,
            ))
        })
        .collect::<Result<Vec<_>>>()?;
    let challenges = old_bulletproof_challenges
        .iter()
        .map(|vector| {
            vector
                .iter()
                .map(|value| parse_fp_decimal(value, "old_bulletproof_challenges"))
                .collect::<Result<Vec<_>>>()
        })
        .collect::<Result<Vec<_>>>()?;
    let proof = pickles::api::MinaWrapProof::from_o1js_json_string(&proof_json)
        .map_err(|err| Error::from_reason(format!("invalid proof JSON: {err:?}")))?;
    match pickles::verify::verify_side_loaded(&app_state, &commitments, &challenges, &proof) {
        Ok(_) => Ok(true),
        Err(pickles::verify::StandaloneVerifyError::VerificationKey(err)) => Err(
            Error::from_reason(format!("invalid side-loaded verification key: {err:?}")),
        ),
        Err(pickles::verify::StandaloneVerifyError::ProofDecoding) => {
            Err(Error::from_reason("invalid wrap wire proof".to_string()))
        }
        Err(_) => Ok(false),
    }
}

/// Direct Rust Pickles smoke API for o1js.
///
/// This intentionally does not call Mina/OCaml Pickles. It compiles and proves
/// a tiny base-case Pickles program in the Rust `pickles` crate, then returns
/// the JSON envelope consumed by `src/lib/proof-system/rust-pickles.ts`.
#[napi(js_name = "rust_pickles_square_base_proof_json")]
pub fn rust_pickles_square_base_proof_json(witness_decimal: String) -> Result<String> {
    let witness = parse_fp_decimal(&witness_decimal, "witness")?;
    let public_state = vec![witness * witness];
    let rule = InductiveRule::new(
        RuleId(0),
        "square_base",
        ProofsVerified::N0,
        SQUARE_STEP_ROUNDS as u8,
    );
    let mut backend =
        BaseCaseRuleBackend::<SquareApp, SQUARE_STEP_ROUNDS, SQUARE_STATEMENT_LEN>::compile(
            &rule, SquareApp,
        )
        .map_err(|err| Error::from_reason(format!("rust pickles compile failed: {err:?}")))?;
    let (_proof, encoded) = backend
        .prove_with_mina_encoding(&public_state, witness)
        .map_err(|err| Error::from_reason(format!("rust pickles prove failed: {err:?}")))?;
    encoded
        .to_o1js_json_string()
        .map_err(|err| Error::from_reason(format!("rust pickles JSON encoding failed: {err:?}")))
}

fn n1_envelope(proved: pickles::recorded::RecordedN1Proof) -> Result<String> {
    let envelope = serde_json::json!({
        "appState": proved
            .app_state
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        "proof": proved.proof.to_o1js_json_value(),
        "challengePolynomialCommitment": [
            proved.challenge_polynomial_commitment.0.to_string(),
            proved.challenge_polynomial_commitment.1.to_string(),
        ],
        "oldBulletproofChallenges": proved
            .old_bulletproof_challenges
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        "dlogPlonkIndex": proved
            .dlog_plonk_index
            .iter()
            .map(|(x, y)| vec![x.to_string(), y.to_string()])
            .collect::<Vec<_>>(),
    });
    serde_json::to_string(&envelope)
        .map_err(|err| Error::from_reason(format!("envelope encoding failed: {err}")))
}

fn stable_n1_envelope(proved: pickles::recorded::RecordedStableN1Proof) -> Result<String> {
    let envelope = serde_json::json!({
        "appState": proved
            .app_state
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        "proof": proved.proof.to_o1js_json_value(),
        "challengePolynomialCommitment": [
            proved.challenge_polynomial_commitment.0.to_string(),
            proved.challenge_polynomial_commitment.1.to_string(),
        ],
        "oldBulletproofChallenges": proved
            .old_bulletproof_challenges
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        "dlogPlonkIndex": proved
            .dlog_plonk_index
            .iter()
            .map(|(x, y)| vec![x.to_string(), y.to_string()])
            .collect::<Vec<_>>(),
        "stableCycles": proved.stable_cycles,
    });
    serde_json::to_string(&envelope)
        .map_err(|err| Error::from_reason(format!("envelope encoding failed: {err}")))
}

fn n2_envelope(proved: pickles::recorded::RecordedN2Proof) -> Result<String> {
    let envelope = serde_json::json!({
        "appState": proved
            .app_state
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        "proof": proved.proof.to_o1js_json_value(),
        "challengePolynomialCommitments": proved
            .challenge_polynomial_commitments
            .iter()
            .map(|(x, y)| vec![x.to_string(), y.to_string()])
            .collect::<Vec<_>>(),
        "oldBulletproofChallenges": proved
            .old_bulletproof_challenges
            .iter()
            .map(|challenges| challenges.iter().map(ToString::to_string).collect::<Vec<_>>())
            .collect::<Vec<_>>(),
        "dlogPlonkIndex": proved
            .dlog_plonk_index
            .iter()
            .map(|(x, y)| vec![x.to_string(), y.to_string()])
            .collect::<Vec<_>>(),
    });
    serde_json::to_string(&envelope)
        .map_err(|err| Error::from_reason(format!("envelope encoding failed: {err}")))
}

/// Proves a recorded circuit through the base-case pipeline, then one
/// recursive (N1) Pickles cycle over the resulting wrap proof. Returns
/// `{ appState, proof, challengePolynomialCommitment,
/// oldBulletproofChallenges, dlogPlonkIndex }` — the last three are the
/// recursion messages `rust_pickles_verify_side_loaded_with_step_vk` needs.
#[napi(js_name = "rust_pickles_prove_recorded_n1")]
pub fn rust_pickles_prove_recorded_n1(
    circuit_json: String,
    witness_decimal: Vec<String>,
) -> Result<String> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    let witness = witness_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "witness"))
        .collect::<Result<Vec<_>>>()?;
    let proved = pickles::recorded::prove_recorded_n1(circuit, witness)
        .map_err(|err| Error::from_reason(format!("rust pickles N1 prove failed: {err:?}")))?;
    n1_envelope(proved)
}

/// Proves a recorded circuit through the base-case pipeline, then the stable
/// same-field N1 recursion loop. `additional_stable_cycles = 0` means two
/// total recursive cycles after the base proof; each increment adds one more
/// stable cycle. Returns the N1 envelope plus `stableCycles`.
#[napi(js_name = "rust_pickles_prove_recorded_stable_n1")]
pub fn rust_pickles_prove_recorded_stable_n1(
    circuit_json: String,
    witness_decimal: Vec<String>,
    additional_stable_cycles: u32,
) -> Result<String> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    let witness = witness_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "witness"))
        .collect::<Result<Vec<_>>>()?;
    let proved = pickles::recorded::prove_recorded_stable_n1(
        circuit,
        witness,
        additional_stable_cycles as usize,
    )
    .map_err(|err| Error::from_reason(format!("rust pickles stable N1 prove failed: {err:?}")))?;
    stable_n1_envelope(proved)
}

/// Proves a true width-2 (`N2`) recorded recursive step over two base proofs
/// of the same recorded circuit. `app_state_decimal` is the public state
/// bound by the N2 digest; the low-level adapter does not derive an
/// aggregation relation from the two previous states.
#[napi(js_name = "rust_pickles_prove_recorded_n2")]
pub fn rust_pickles_prove_recorded_n2(
    circuit_json: String,
    first_witness_decimal: Vec<String>,
    second_witness_decimal: Vec<String>,
    app_state_decimal: Vec<String>,
) -> Result<String> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    let first_witness = first_witness_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "first_witness"))
        .collect::<Result<Vec<_>>>()?;
    let second_witness = second_witness_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "second_witness"))
        .collect::<Result<Vec<_>>>()?;
    let app_state = app_state_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "app_state"))
        .collect::<Result<Vec<_>>>()?;
    let proved =
        pickles::recorded::prove_recorded_n2(circuit, first_witness, second_witness, app_state)
            .map_err(|err| Error::from_reason(format!("rust pickles N2 prove failed: {err:?}")))?;
    n2_envelope(proved)
}

/// [`rust_pickles_verify_side_loaded`] with an explicit `dlog_plonk_index`
/// (the wrap VK commitments bound by the statement digest — the
/// `dlogPlonkIndex` of an N1 envelope), as `[["x","y"], ...]`.
#[napi(js_name = "rust_pickles_verify_side_loaded_with_step_vk")]
pub fn rust_pickles_verify_side_loaded_with_step_vk(
    app_state_decimal: Vec<String>,
    dlog_plonk_index: Vec<Vec<String>>,
    challenge_polynomial_commitments: Vec<Vec<String>>,
    old_bulletproof_challenges: Vec<Vec<String>>,
    proof_json: String,
) -> Result<bool> {
    let app_state = app_state_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "app_state"))
        .collect::<Result<Vec<_>>>()?;
    let parse_points = |pairs: &[Vec<String>], name: &str| {
        pairs
            .iter()
            .map(|pair| {
                if pair.len() != 2 {
                    return Err(Error::from_reason(format!(
                        "{name}: expected [x, y] decimal pairs"
                    )));
                }
                Ok((
                    parse_fp_decimal(&pair[0], name)?,
                    parse_fp_decimal(&pair[1], name)?,
                ))
            })
            .collect::<Result<Vec<_>>>()
    };
    let dlog_index = parse_points(&dlog_plonk_index, "dlog_plonk_index")?;
    let commitments = parse_points(
        &challenge_polynomial_commitments,
        "challenge_polynomial_commitments",
    )?;
    let challenges = old_bulletproof_challenges
        .iter()
        .map(|vector| {
            vector
                .iter()
                .map(|value| parse_fp_decimal(value, "old_bulletproof_challenges"))
                .collect::<Result<Vec<_>>>()
        })
        .collect::<Result<Vec<_>>>()?;
    let proof = pickles::api::MinaWrapProof::from_o1js_json_string(&proof_json)
        .map_err(|err| Error::from_reason(format!("invalid proof JSON: {err:?}")))?;
    match pickles::verify::verify_side_loaded_with_step_vk(
        &app_state,
        Some(&dlog_index),
        &commitments,
        &challenges,
        &proof,
    ) {
        Ok(_) => Ok(true),
        Err(pickles::verify::StandaloneVerifyError::VerificationKey(err)) => Err(
            Error::from_reason(format!("invalid side-loaded verification key: {err:?}")),
        ),
        Err(pickles::verify::StandaloneVerifyError::ProofDecoding) => {
            Err(Error::from_reason("invalid wrap wire proof".to_string()))
        }
        Err(_) => Ok(false),
    }
}

/// [`rust_pickles_prove_recorded_base`], but keeps the full base proof alive
/// in an opaque native handle so a later `rust_pickles_prove_recorded_n1_over`
/// call can recursively verify it (the ZkProgram `SelfProof` shape). Use
/// `rust_pickles_recorded_base_envelope` to read its `{ appState, proof }`.
#[napi(js_name = "rust_pickles_prove_recorded_base_keep")]
pub fn rust_pickles_prove_recorded_base_keep(
    circuit_json: String,
    witness_decimal: Vec<String>,
) -> Result<External<pickles::recorded::RecordedBaseHandle>> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    let witness = witness_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "witness"))
        .collect::<Result<Vec<_>>>()?;
    let handle = pickles::recorded::prove_recorded_base_case_keep(circuit, witness)
        .map_err(|err| Error::from_reason(format!("rust pickles prove failed: {err:?}")))?;
    Ok(External::new(handle))
}

/// Compiles and retains the Step/Wrap prover indexes of a recorded base
/// circuit. The returned handle can prove multiple witnesses without
/// rebuilding either index.
#[napi(js_name = "rust_pickles_compile_recorded_base")]
pub fn rust_pickles_compile_recorded_base(
    circuit_json: String,
    witness_decimal: Vec<String>,
) -> Result<External<pickles::recorded::RecordedCompiledBase>> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    let witness = witness_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "witness"))
        .collect::<Result<Vec<_>>>()?;
    let compiled = pickles::recorded::RecordedCompiledBase::compile(circuit, witness)
        .map_err(|err| Error::from_reason(format!("rust pickles compile failed: {err:?}")))?;
    Ok(External::new(compiled))
}

#[napi(js_name = "rust_pickles_compile_recorded_base_bytes")]
pub fn rust_pickles_compile_recorded_base_bytes(
    circuit_json: String,
    witness_bytes: Uint8Array,
) -> Result<External<pickles::recorded::RecordedCompiledBase>> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_bytes(witness_bytes.as_ref(), "witness")?;
    let compiled = pickles::recorded::RecordedCompiledBase::compile(circuit, witness)
        .map_err(|err| Error::from_reason(format!("rust pickles compile failed: {err:?}")))?;
    Ok(External::new(compiled))
}

fn parse_recorded_program_branches(
    branches_json: &str,
) -> Result<Vec<pickles::recorded::RecordedProgramBranch>> {
    #[derive(serde::Deserialize)]
    struct Branch {
        circuit: pickles::recorded::RecordedCircuit,
        witness: Vec<String>,
        #[serde(rename = "proofsVerified")]
        proofs_verified: u8,
    }
    let branches: Vec<Branch> = serde_json::from_str(branches_json)
        .map_err(|err| Error::from_reason(format!("invalid program JSON: {err}")))?;
    branches
        .into_iter()
        .map(|branch| {
            let witness = branch
                .witness
                .iter()
                .map(|value| parse_fp_decimal(value, "witness"))
                .collect::<Result<Vec<_>>>()?;
            Ok(pickles::recorded::RecordedProgramBranch {
                circuit: branch.circuit,
                witness,
                proofs_verified: branch.proofs_verified,
            })
        })
        .collect()
}

/// Native direct-binding counterpart of the browser's shared width-0
/// multi-branch program. It owns every Step index and one shared Wrap index.
#[napi(js_name = "rust_pickles_compile_recorded_program_shared")]
pub fn rust_pickles_compile_recorded_program_shared(
    branches_json: String,
) -> Result<External<pickles::recorded::RecordedCompiledBaseProgram>> {
    let branches = parse_recorded_program_branches(&branches_json)?;
    let compiled = pickles::recorded::RecordedCompiledBaseProgram::compile(branches)
        .map_err(|err| Error::from_reason(format!("program compile failed: {err:?}")))?;
    Ok(External::new(compiled))
}

#[napi(js_name = "rust_pickles_recorded_program_vk_envelope")]
pub fn rust_pickles_recorded_program_vk_envelope(
    program: &External<pickles::recorded::RecordedCompiledBaseProgram>,
) -> Result<String> {
    let (base64, hash) = program
        .verification_key_envelope()
        .map_err(|err| Error::from_reason(format!("program VK envelope failed: {err:?}")))?;
    serde_json::to_string(&serde_json::json!({ "base64": base64, "hash": hash }))
        .map_err(|err| Error::from_reason(format!("VK envelope encoding failed: {err}")))
}

#[napi(js_name = "rust_pickles_program_prove_n0_bytes")]
pub fn rust_pickles_program_prove_n0_bytes(
    program: &mut External<pickles::recorded::RecordedCompiledBaseProgram>,
    branch_index: u32,
    witness_bytes: Uint8Array,
) -> Result<External<pickles::recorded::RecordedBaseHandle>> {
    let witness = parse_fp_bytes(witness_bytes.as_ref(), "witness")?;
    let handle = program
        .prove_keep(branch_index as usize, witness)
        .map_err(|err| Error::from_reason(format!("program N0 proving failed: {err:?}")))?;
    Ok(External::new(handle))
}

#[napi(js_name = "rust_pickles_recorded_base_cache_key")]
pub fn rust_pickles_recorded_base_cache_key(circuit_json: String) -> Result<String> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    Ok(pickles::recorded::RecordedCompiledBase::cache_key(&circuit))
}

#[napi(js_name = "rust_pickles_recorded_base_cache_bytes")]
pub fn rust_pickles_recorded_base_cache_bytes(
    compiled: &External<pickles::recorded::RecordedCompiledBase>,
) -> Result<Uint8Array> {
    compiled
        .to_cache_bytes()
        .map(Uint8Array::from)
        .map_err(|err| Error::from_reason(format!("failed to serialize Rust Pickles cache: {err}")))
}

#[napi(js_name = "rust_pickles_compile_recorded_base_from_cache_bytes")]
pub fn rust_pickles_compile_recorded_base_from_cache_bytes(
    circuit_json: String,
    witness_bytes: Uint8Array,
    cache_bytes: Uint8Array,
) -> Result<External<pickles::recorded::RecordedCompiledBase>> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_bytes(witness_bytes.as_ref(), "witness")?;
    let compiled = pickles::recorded::RecordedCompiledBase::from_cache_bytes(
        circuit,
        witness,
        cache_bytes.as_ref(),
    )
    .map_err(|err| Error::from_reason(format!("invalid Rust Pickles cache: {err}")))?;
    Ok(External::new(compiled))
}

#[napi(js_name = "rust_pickles_prove_recorded_base_keep_compiled")]
pub fn rust_pickles_prove_recorded_base_keep_compiled(
    compiled: &mut External<pickles::recorded::RecordedCompiledBase>,
    witness_decimal: Vec<String>,
) -> Result<External<pickles::recorded::RecordedBaseHandle>> {
    let witness = witness_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "witness"))
        .collect::<Result<Vec<_>>>()?;
    let handle = compiled
        .prove_keep(witness)
        .map_err(|err| Error::from_reason(format!("rust pickles prove failed: {err:?}")))?;
    Ok(External::new(handle))
}

#[napi(js_name = "rust_pickles_prove_recorded_base_keep_compiled_bytes")]
pub fn rust_pickles_prove_recorded_base_keep_compiled_bytes(
    compiled: &mut External<pickles::recorded::RecordedCompiledBase>,
    witness_bytes: Uint8Array,
) -> Result<External<pickles::recorded::RecordedBaseHandle>> {
    let witness = parse_fp_bytes(witness_bytes.as_ref(), "witness")?;
    let handle = compiled
        .prove_keep(witness)
        .map_err(|err| Error::from_reason(format!("rust pickles prove failed: {err:?}")))?;
    Ok(External::new(handle))
}

/// Assembles the compile-time proof template as a proof-SHAPED donor from
/// the compiled base indexes — no prover runs during compilation (the donor
/// is proven index-equivalent to a real base proof in pickles).
#[napi(js_name = "rust_pickles_recorded_base_donor_handle_bytes")]
pub fn rust_pickles_recorded_base_donor_handle_bytes(
    compiled: &External<pickles::recorded::RecordedCompiledBase>,
    witness_bytes: Uint8Array,
) -> Result<External<pickles::recorded::RecordedBaseHandle>> {
    let witness = parse_fp_bytes(witness_bytes.as_ref(), "witness")?;
    let handle = compiled
        .donor_handle(&witness)
        .map_err(|err| Error::from_reason(format!("rust pickles donor template failed: {err:?}")))?;
    Ok(External::new(handle))
}

/// Canonical Mina side-loaded VK of a compiled base circuit:
/// `{"base64": ..., "hash": ...}` — the same data/hash pair jsoo's
/// `Program.compile()` returns.
#[napi(js_name = "rust_pickles_recorded_base_vk_envelope")]
pub fn rust_pickles_recorded_base_vk_envelope(
    compiled: &External<pickles::recorded::RecordedCompiledBase>,
) -> Result<String> {
    let (base64, hash) = compiled
        .verification_key_envelope()
        .map_err(|err| Error::from_reason(format!("VK envelope failed: {err:?}")))?;
    serde_json::to_string(&serde_json::json!({ "base64": base64, "hash": hash }))
        .map_err(|err| Error::from_reason(format!("envelope encoding failed: {err}")))
}

#[napi(js_name = "rust_pickles_prove_recorded_n2_over_base_handles")]
pub fn rust_pickles_prove_recorded_n2_over_base_handles(
    first: &External<pickles::recorded::RecordedBaseHandle>,
    second: &External<pickles::recorded::RecordedBaseHandle>,
    circuit_json: String,
    witness_decimal: Vec<String>,
) -> Result<String> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    let witness = witness_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "witness"))
        .collect::<Result<Vec<_>>>()?;
    let proved =
        pickles::recorded::prove_recorded_n2_over_base_handles(first, second, circuit, witness)
            .map_err(|err| Error::from_reason(format!("rust pickles N2 prove failed: {err:?}")))?;
    n2_envelope(proved)
}

#[napi(js_name = "rust_pickles_prove_recorded_n2_over_base_handles_bytes")]
pub fn rust_pickles_prove_recorded_n2_over_base_handles_bytes(
    first: &External<pickles::recorded::RecordedBaseHandle>,
    second: &External<pickles::recorded::RecordedBaseHandle>,
    circuit_json: String,
    witness_bytes: Uint8Array,
) -> Result<String> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_bytes(witness_bytes.as_ref(), "witness")?;
    let proved =
        pickles::recorded::prove_recorded_n2_over_base_handles(first, second, circuit, witness)
            .map_err(|err| Error::from_reason(format!("rust pickles N2 prove failed: {err:?}")))?;
    n2_envelope(proved)
}

#[napi(js_name = "rust_pickles_compile_recorded_n2")]
pub fn rust_pickles_compile_recorded_n2(
    first: &External<pickles::recorded::RecordedBaseHandle>,
    second: &External<pickles::recorded::RecordedBaseHandle>,
    circuit_json: String,
    witness_decimal: Vec<String>,
) -> Result<External<pickles::recorded::RecordedCompiledN2>> {
    let circuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    let witness = witness_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "witness"))
        .collect::<Result<Vec<_>>>()?;
    let compiled = pickles::recorded::RecordedCompiledN2::compile(first, second, circuit, witness)
        .map_err(|err| Error::from_reason(format!("rust pickles N2 compile failed: {err:?}")))?;
    Ok(External::new(compiled))
}

#[napi(js_name = "rust_pickles_compile_recorded_n2_bytes")]
pub fn rust_pickles_compile_recorded_n2_bytes(
    first: &External<pickles::recorded::RecordedBaseHandle>,
    second: &External<pickles::recorded::RecordedBaseHandle>,
    circuit_json: String,
    witness_bytes: Uint8Array,
) -> Result<External<pickles::recorded::RecordedCompiledN2>> {
    let circuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_bytes(witness_bytes.as_ref(), "witness")?;
    let compiled = pickles::recorded::RecordedCompiledN2::compile(first, second, circuit, witness)
        .map_err(|err| Error::from_reason(format!("rust pickles N2 compile failed: {err:?}")))?;
    Ok(External::new(compiled))
}

#[napi(js_name = "rust_pickles_prove_recorded_n2_compiled_bytes")]
pub fn rust_pickles_prove_recorded_n2_compiled_bytes(
    compiled: &mut External<pickles::recorded::RecordedCompiledN2>,
    first: &External<pickles::recorded::RecordedBaseHandle>,
    second: &External<pickles::recorded::RecordedBaseHandle>,
    witness_bytes: Uint8Array,
) -> Result<String> {
    let witness = parse_fp_bytes(witness_bytes.as_ref(), "witness")?;
    let proved = compiled
        .prove(first, second, witness)
        .map_err(|err| Error::from_reason(format!("rust pickles N2 prove failed: {err:?}")))?;
    n2_envelope(proved)
}

#[napi(js_name = "rust_pickles_compile_recorded_n1")]
pub fn rust_pickles_compile_recorded_n1(
    previous: &External<pickles::recorded::RecordedBaseHandle>,
    circuit_json: String,
    witness_decimal: Vec<String>,
) -> Result<External<pickles::recorded::RecordedCompiledN1>> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    let witness = witness_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "witness"))
        .collect::<Result<Vec<_>>>()?;
    let compiled = pickles::recorded::RecordedCompiledN1::compile(previous, circuit, witness)
        .map_err(|err| Error::from_reason(format!("rust pickles N1 compile failed: {err:?}")))?;
    Ok(External::new(compiled))
}

#[napi(js_name = "rust_pickles_compile_recorded_n1_bytes")]
pub fn rust_pickles_compile_recorded_n1_bytes(
    previous: &External<pickles::recorded::RecordedBaseHandle>,
    circuit_json: String,
    witness_bytes: Uint8Array,
) -> Result<External<pickles::recorded::RecordedCompiledN1>> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_bytes(witness_bytes.as_ref(), "witness")?;
    let compiled = pickles::recorded::RecordedCompiledN1::compile(previous, circuit, witness)
        .map_err(|err| Error::from_reason(format!("rust pickles N1 compile failed: {err:?}")))?;
    Ok(External::new(compiled))
}

#[napi(js_name = "rust_pickles_prove_recorded_n1_compiled")]
pub fn rust_pickles_prove_recorded_n1_compiled(
    compiled: &mut External<pickles::recorded::RecordedCompiledN1>,
    previous: &External<pickles::recorded::RecordedBaseHandle>,
    witness_decimal: Vec<String>,
) -> Result<String> {
    let witness = witness_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "witness"))
        .collect::<Result<Vec<_>>>()?;
    let handle = compiled
        .prove_keep(previous, witness)
        .map_err(|err| Error::from_reason(format!("rust pickles N1 prove failed: {err:?}")))?;
    let proved = handle
        .to_recorded_n1_proof()
        .ok_or_else(|| Error::from_reason("compiled N1 did not return a recursive proof"))?;
    n1_envelope(proved)
}

#[napi(js_name = "rust_pickles_prove_recorded_n1_compiled_bytes")]
pub fn rust_pickles_prove_recorded_n1_compiled_bytes(
    compiled: &mut External<pickles::recorded::RecordedCompiledN1>,
    previous: &External<pickles::recorded::RecordedBaseHandle>,
    witness_bytes: Uint8Array,
) -> Result<String> {
    let witness = parse_fp_bytes(witness_bytes.as_ref(), "witness")?;
    let handle = compiled
        .prove_keep(previous, witness)
        .map_err(|err| Error::from_reason(format!("rust pickles N1 prove failed: {err:?}")))?;
    let proved = handle
        .to_recorded_n1_proof()
        .ok_or_else(|| Error::from_reason("compiled N1 did not return a recursive proof"))?;
    n1_envelope(proved)
}

#[napi(js_name = "rust_pickles_prove_recorded_n1_compiled_keep")]
pub fn rust_pickles_prove_recorded_n1_compiled_keep(
    compiled: &mut External<pickles::recorded::RecordedCompiledN1>,
    previous: &External<pickles::recorded::RecordedBaseHandle>,
    witness_decimal: Vec<String>,
) -> Result<External<pickles::recorded::RecordedBaseHandle>> {
    let witness = witness_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "witness"))
        .collect::<Result<Vec<_>>>()?;
    let handle = compiled
        .prove_keep(previous, witness)
        .map_err(|err| Error::from_reason(format!("rust pickles N1 prove failed: {err:?}")))?;
    Ok(External::new(handle))
}

#[napi(js_name = "rust_pickles_prove_recorded_n1_compiled_keep_bytes")]
pub fn rust_pickles_prove_recorded_n1_compiled_keep_bytes(
    compiled: &mut External<pickles::recorded::RecordedCompiledN1>,
    previous: &External<pickles::recorded::RecordedBaseHandle>,
    witness_bytes: Uint8Array,
) -> Result<External<pickles::recorded::RecordedBaseHandle>> {
    let witness = parse_fp_bytes(witness_bytes.as_ref(), "witness")?;
    let handle = compiled
        .prove_keep(previous, witness)
        .map_err(|err| Error::from_reason(format!("rust pickles N1 prove failed: {err:?}")))?;
    Ok(External::new(handle))
}

#[napi(js_name = "rust_pickles_recorded_n1_envelope")]
pub fn rust_pickles_recorded_n1_envelope(
    handle: &External<pickles::recorded::RecordedBaseHandle>,
) -> Result<String> {
    let proved = handle
        .to_recorded_n1_proof()
        .ok_or_else(|| Error::from_reason("proof handle is not recursive"))?;
    n1_envelope(proved)
}

/// The `{ appState, proof }` envelope of a kept base proof — the same shape
/// `rust_pickles_prove_recorded_base` returns.
#[napi(js_name = "rust_pickles_recorded_base_envelope")]
pub fn rust_pickles_recorded_base_envelope(
    handle: &External<pickles::recorded::RecordedBaseHandle>,
) -> Result<String> {
    let proved = handle.to_recorded_proof();
    let envelope = serde_json::json!({
        "appState": proved
            .app_state
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        "proof": proved.proof.to_o1js_json_value(),
    });
    serde_json::to_string(&envelope)
        .map_err(|err| Error::from_reason(format!("envelope encoding failed: {err}")))
}

/// The canonical Mina account-update authorization proof for a kept N0
/// proof. Keep the native API identical to the browser WASM binding so the
/// high-level SmartContract prover can serialize either transport.
#[napi(js_name = "rust_pickles_recorded_base_transaction_base64")]
pub fn rust_pickles_recorded_base_transaction_base64(
    handle: &External<pickles::recorded::RecordedBaseHandle>,
) -> Result<String> {
    handle
        .to_transaction_base64()
        .map_err(|err| Error::from_reason(format!("transaction proof encoding failed: {err:?}")))
}

/// Proves one recursive (N1) Pickles cycle whose step *runs a new recorded
/// circuit* while verifying a previously kept base proof. Returns the same
/// envelope as `rust_pickles_prove_recorded_n1`; the digest binds the new
/// circuit's `appState`.
#[napi(js_name = "rust_pickles_prove_recorded_n1_over")]
pub fn rust_pickles_prove_recorded_n1_over(
    handle: &External<pickles::recorded::RecordedBaseHandle>,
    circuit_json: String,
    witness_decimal: Vec<String>,
) -> Result<String> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    let witness = witness_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "witness"))
        .collect::<Result<Vec<_>>>()?;
    let proved = pickles::recorded::prove_recorded_n1_over(handle, circuit, witness)
        .map_err(|err| Error::from_reason(format!("rust pickles N1-over prove failed: {err:?}")))?;
    n1_envelope(proved)
}

/// Decodes a side-loaded verification key into its structured JSON form:
/// `{ maxProofsVerified, actualWrapDomainSize, commitments: [["x","y"], ...] }`.
/// `format` is `"base58"` (Mina network Base58Check) or `"base64"` (the raw
/// bin_prot bytes base64-encoded — what o1js `verificationKey.data` holds).
#[napi(js_name = "rust_pickles_decode_side_loaded_vk")]
pub fn rust_pickles_decode_side_loaded_vk(encoded: String, format: String) -> Result<String> {
    use base64::prelude::*;
    let key = match format.as_str() {
        "base58" => {
            pickles::mina_bin_prot::SideLoadedVerificationKeyV2::from_base58_check(&encoded)
                .map_err(|err| Error::from_reason(format!("invalid base58 VK: {err:?}")))?
        }
        "base64" => {
            let bytes = BASE64_STANDARD
                .decode(encoded)
                .map_err(|err| Error::from_reason(format!("invalid base64: {err}")))?;
            pickles::mina_bin_prot::SideLoadedVerificationKeyV2::from_bin_prot(&bytes)
                .map_err(|err| Error::from_reason(format!("invalid VK bin_prot: {err:?}")))?
        }
        other => return Err(Error::from_reason(format!("unknown VK format '{other}'"))),
    };
    let envelope = serde_json::json!({
        "maxProofsVerified": key.max_proofs_verified.to_usize(),
        "actualWrapDomainSize": key.actual_wrap_domain_size.to_usize(),
        "minaHash": key.mina_hash().to_string(),
        "base64": BASE64_STANDARD.encode(
            key.to_bin_prot()
                .map_err(|err| Error::from_reason(format!("VK bin_prot encoding failed: {err:?}")))?
        ),
        "base58": key
            .to_base58_check()
            .map_err(|err| Error::from_reason(format!("VK base58 encoding failed: {err:?}")))?,
        "commitments": key
            .commitments
            .iter()
            .map(|(x, y)| vec![x.to_string(), y.to_string()])
            .collect::<Vec<_>>(),
    });
    serde_json::to_string(&envelope)
        .map_err(|err| Error::from_reason(format!("envelope encoding failed: {err}")))
}

/// Serializes the full Rust Pickles *step* circuit hosting a recorded o1js
/// circuit, in the same `{ public_input_size, gates }` JSON schema as the
/// jsoo wasm's `prover_to_json` — the tool behind the gate-level parity diff
/// against OCaml Pickles step circuits.
#[napi(js_name = "rust_pickles_recorded_step_circuit_json")]
pub fn rust_pickles_recorded_step_circuit_json(circuit_json: String) -> Result<String> {
    use snarky::api::SnarkyCircuit as _;

    #[derive(serde::Serialize)]
    struct Circuit {
        public_input_size: usize,
        gates: Vec<kimchi::circuits::gate::CircuitGate<Fp>>,
    }

    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    circuit
        .validate()
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit: {err:?}")))?;
    let app = pickles::recorded::RecordedApp { circuit };
    let (prover, _verifier) = pickles::api::StepCircuit { app }
        .compile_to_indexes()
        .map_err(|err| Error::from_reason(format!("step compile failed: {err:?}")))?;
    let circuit = Circuit {
        public_input_size: prover.index.cs.public,
        gates: prover.index.cs.gates.to_vec(),
    };
    serde_json::to_string(&circuit)
        .map_err(|err| Error::from_reason(format!("circuit encoding failed: {err}")))
}

/// Compiles a shared-wrap program and dumps every branch step circuit plus
/// the shared wrap circuit (`{ steps: [{public_input_size, gates}], wrap }`)
/// — the Rust half of the multi-branch gates parity diff.
#[napi(js_name = "rust_pickles_recorded_program_circuits_json")]
pub fn rust_pickles_recorded_program_circuits_json(branches_json: String) -> Result<String> {
    #[derive(serde::Deserialize)]
    struct Branch {
        circuit: pickles::recorded::RecordedCircuit,
        witness: Vec<String>,
        #[serde(rename = "proofsVerified")]
        proofs_verified: u8,
    }
    let branches: Vec<Branch> = serde_json::from_str(&branches_json)
        .map_err(|err| Error::from_reason(format!("invalid program JSON: {err}")))?;
    let mut parsed = Vec::with_capacity(branches.len());
    for branch in branches {
        let witness = branch
            .witness
            .iter()
            .map(|value| parse_fp_decimal(value, "witness"))
            .collect::<Result<Vec<_>>>()?;
        parsed.push(pickles::recorded::RecordedProgramBranch {
            circuit: branch.circuit,
            witness,
            proofs_verified: branch.proofs_verified,
        });
    }
    pickles::recorded::dump_recorded_program_circuits(parsed)
        .map_err(|err| Error::from_reason(format!("program dump failed: {err:?}")))
}

/// Serializes the wrap circuit of a recorded base-case program in the same
/// `{ public_input_size, gates }` JSON schema as the jsoo wasm's
/// `fq_prover_to_json` — the Rust half of the wrap-circuit parity diff.
/// Runs the full two-pass compile (a real base proof), so this takes seconds.
#[napi(js_name = "rust_pickles_recorded_wrap_circuit_json")]
pub fn rust_pickles_recorded_wrap_circuit_json(
    circuit_json: String,
    witness_decimal: Vec<String>,
) -> Result<String> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| Error::from_reason(format!("invalid recorded circuit JSON: {err}")))?;
    let witness = witness_decimal
        .iter()
        .map(|value| parse_fp_decimal(value, "witness"))
        .collect::<Result<Vec<_>>>()?;
    pickles::recorded::dump_recorded_wrap_circuit(circuit, witness)
        .map_err(|err| Error::from_reason(format!("wrap circuit dump failed: {err:?}")))
}

/// Decodes a Mina side-loaded proof (base64 of the bin_prot bytes — what
/// o1js `proof.toJSON().proof` holds) into its structural JSON: the
/// flattened wrap statement (decimal Fq strings), the wrap proof's IPA round
/// count and the recursion message shapes. Ground truth for statement-layout
/// and codec parity against jsoo proofs.
#[napi(js_name = "rust_pickles_decode_mina_proof_base64")]
pub fn rust_pickles_decode_mina_proof_base64(proof_base64: String) -> Result<String> {
    use base64::prelude::*;
    let bytes = BASE64_STANDARD
        .decode(proof_base64)
        .map_err(|err| Error::from_reason(format!("invalid base64: {err}")))?;
    let proof = pickles::mina_bin_prot::WrapProofBaseV3::from_mina_bin_prot(&bytes)
        .or_else(|_| pickles::mina_bin_prot::WrapProofBaseV3::from_normalized_bin_prot(&bytes))
        .map_err(|err| Error::from_reason(format!("proof bin_prot decoding failed: {err:?}")))?;
    let envelope = serde_json::json!({
        "statement": proof
            .statement
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        "wrapIpaRounds": proof.proof.bulletproof_lr.len(),
        "messagesForNextWrap": {
            "oldBulletproofChallenges": proof
                .stable_statement
                .messages_for_next_wrap_proof
                .old_bulletproof_challenges
                .iter()
                .map(|v| v.len())
                .collect::<Vec<_>>(),
        },
        "messagesForNextStep": {
            "challengePolynomialCommitments": proof
                .stable_statement
                .messages_for_next_step_proof
                .challenge_polynomial_commitments
                .len(),
            "oldBulletproofChallenges": proof
                .stable_statement
                .messages_for_next_step_proof
                .old_bulletproof_challenges
                .iter()
                .map(|v| v.len())
                .collect::<Vec<_>>(),
        },
    });
    serde_json::to_string(&envelope)
        .map_err(|err| Error::from_reason(format!("envelope encoding failed: {err}")))
}
