//! Pickles surface for JS: recorded-circuit base-case proving and standalone
//! side-loaded verification. Mirrors `kimchi-napi/src/pickles.rs` so o1js can
//! run the same flows in the browser (WASM) and in Node (NAPI).

use core::str::FromStr;

use ark_serialize::CanonicalDeserialize;
use mina_curves::pasta::Fp;
use wasm_bindgen::prelude::*;

fn parse_fp_decimal(value: &str, name: &str) -> Result<Fp, JsError> {
    Fp::from_str(value)
        .map_err(|_| JsError::new(&format!("{name}: expected decimal Pasta Fp field")))
}

fn parse_fp_decimals(values: Vec<String>, name: &str) -> Result<Vec<Fp>, JsError> {
    values
        .iter()
        .map(|value| parse_fp_decimal(value, name))
        .collect()
}

fn parse_fp_bytes(bytes: &[u8], name: &str) -> Result<Vec<Fp>, JsError> {
    const FIELD_BYTES: usize = 32;
    if !bytes.len().is_multiple_of(FIELD_BYTES) {
        return Err(JsError::new(&format!(
            "{name}: expected a multiple of {FIELD_BYTES} canonical Fp bytes"
        )));
    }
    bytes
        .chunks_exact(FIELD_BYTES)
        .map(|chunk| {
            Fp::deserialize_compressed(chunk)
                .map_err(|_| JsError::new(&format!("{name}: non-canonical Pasta Fp encoding")))
        })
        .collect()
}

fn recorded_n1_envelope(
    app_state: &[Fp],
    proof: &pickles::api::MinaWrapProof,
    challenge_polynomial_commitment: &(Fp, Fp),
    old_bulletproof_challenges: &[Fp],
    dlog_plonk_index: &[(Fp, Fp)],
    stable_cycles: Option<usize>,
) -> Result<String, JsError> {
    let mut envelope = serde_json::json!({
        "appState": app_state
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        "proof": proof.to_o1js_json_value(),
        "challengePolynomialCommitment": [
            challenge_polynomial_commitment.0.to_string(),
            challenge_polynomial_commitment.1.to_string(),
        ],
        "oldBulletproofChallenges": old_bulletproof_challenges
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        "dlogPlonkIndex": dlog_plonk_index
            .iter()
            .map(|(x, y)| vec![x.to_string(), y.to_string()])
            .collect::<Vec<_>>(),
    });
    if let Some(stable_cycles) = stable_cycles {
        envelope["stableCycles"] = serde_json::json!(stable_cycles);
    }
    serde_json::to_string(&envelope)
        .map_err(|err| JsError::new(&format!("envelope encoding failed: {err}")))
}

fn recorded_n2_envelope(proved: pickles::recorded::RecordedN2Proof) -> Result<String, JsError> {
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
        .map_err(|err| JsError::new(&format!("envelope encoding failed: {err}")))
}

/// Proves a recorded circuit (the `pickles::recorded::RecordedCircuit` JSON
/// envelope produced by o1js's constraint-system adapter) through the
/// base-case Pickles pipeline, with the witness variable values as decimal
/// Fp strings. Returns `{ appState, proof }` as JSON, where `proof` is the
/// o1js wrap proof envelope.
#[wasm_bindgen]
pub fn rust_pickles_prove_recorded_base(
    circuit_json: String,
    witness_decimal: Vec<String>,
) -> Result<String, JsError> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| JsError::new(&format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_decimals(witness_decimal, "witness")?;
    let proved =
        crate::rayon::run_in_pool(|| pickles::recorded::prove_recorded_base_case(circuit, witness))
            .map_err(|err| JsError::new(&format!("rust pickles prove failed: {err:?}")))?;
    let envelope = serde_json::json!({
        "appState": proved
            .app_state
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        "proof": proved.proof.to_o1js_json_value(),
    });
    serde_json::to_string(&envelope)
        .map_err(|err| JsError::new(&format!("envelope encoding failed: {err}")))
}

/// Verifies a Pickles wrap proof (the o1js JSON envelope) against the
/// side-loaded verification key it embeds — no prover backend.
///
/// `app_state_decimal` is the claimed application state as decimal Fp
/// strings. `challenge_polynomial_commitments_json` /
/// `old_bulletproof_challenges_json` are the recursion messages of the
/// proofs this one verified, as JSON (`[["x","y"], ...]` and
/// `[["c0","c1",...], ...]`) — `"[]"` for a base-case proof.
#[wasm_bindgen]
pub fn rust_pickles_verify_side_loaded(
    app_state_decimal: Vec<String>,
    challenge_polynomial_commitments_json: String,
    old_bulletproof_challenges_json: String,
    proof_json: String,
) -> Result<bool, JsError> {
    let app_state = parse_fp_decimals(app_state_decimal, "app_state")?;
    let commitments =
        serde_json::from_str::<Vec<(String, String)>>(&challenge_polynomial_commitments_json)
            .map_err(|err| {
                JsError::new(&format!("invalid challenge_polynomial_commitments: {err}"))
            })?
            .iter()
            .map(|(x, y)| {
                Ok((
                    parse_fp_decimal(x, "commitment x")?,
                    parse_fp_decimal(y, "commitment y")?,
                ))
            })
            .collect::<Result<Vec<_>, JsError>>()?;
    let challenges = serde_json::from_str::<Vec<Vec<String>>>(&old_bulletproof_challenges_json)
        .map_err(|err| JsError::new(&format!("invalid old_bulletproof_challenges: {err}")))?
        .into_iter()
        .map(|vector| parse_fp_decimals(vector, "old_bulletproof_challenges"))
        .collect::<Result<Vec<_>, JsError>>()?;
    let proof = pickles::api::MinaWrapProof::from_o1js_json_string(&proof_json)
        .map_err(|err| JsError::new(&format!("invalid proof JSON: {err:?}")))?;
    let verified = crate::rayon::run_in_pool(|| {
        pickles::verify::verify_side_loaded(&app_state, &commitments, &challenges, &proof)
    });
    match verified {
        Ok(_) => Ok(true),
        Err(pickles::verify::StandaloneVerifyError::VerificationKey(err)) => Err(JsError::new(
            &format!("invalid side-loaded verification key: {err:?}"),
        )),
        Err(pickles::verify::StandaloneVerifyError::ProofDecoding) => {
            Err(JsError::new("invalid wrap wire proof"))
        }
        Err(_) => Ok(false),
    }
}

/// Proves a recorded circuit through the base-case pipeline, then one
/// recursive (N1) Pickles cycle over the resulting wrap proof. Returns
/// `{ appState, proof, challengePolynomialCommitment,
/// oldBulletproofChallenges, dlogPlonkIndex }` as JSON — the last three are
/// the recursion messages `rust_pickles_verify_side_loaded_with_step_vk`
/// needs.
#[wasm_bindgen]
pub fn rust_pickles_prove_recorded_n1(
    circuit_json: String,
    witness_decimal: Vec<String>,
) -> Result<String, JsError> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| JsError::new(&format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_decimals(witness_decimal, "witness")?;
    let proved =
        crate::rayon::run_in_pool(|| pickles::recorded::prove_recorded_n1(circuit, witness))
            .map_err(|err| JsError::new(&format!("rust pickles N1 prove failed: {err:?}")))?;
    recorded_n1_envelope(
        &proved.app_state,
        &proved.proof,
        &proved.challenge_polynomial_commitment,
        &proved.old_bulletproof_challenges,
        &proved.dlog_plonk_index,
        None,
    )
}

/// Proves a recorded circuit through the base-case pipeline, then the stable
/// same-field N1 recursion loop. `additional_stable_cycles = 0` means two
/// total recursive cycles after the base proof; each increment adds one more
/// stable cycle. Returns the N1 envelope plus `stableCycles`.
#[wasm_bindgen]
pub fn rust_pickles_prove_recorded_stable_n1(
    circuit_json: String,
    witness_decimal: Vec<String>,
    additional_stable_cycles: u32,
) -> Result<String, JsError> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| JsError::new(&format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_decimals(witness_decimal, "witness")?;
    let proved = crate::rayon::run_in_pool(|| {
        pickles::recorded::prove_recorded_stable_n1(
            circuit,
            witness,
            additional_stable_cycles as usize,
        )
    })
    .map_err(|err| JsError::new(&format!("rust pickles stable N1 prove failed: {err:?}")))?;
    recorded_n1_envelope(
        &proved.app_state,
        &proved.proof,
        &proved.challenge_polynomial_commitment,
        &proved.old_bulletproof_challenges,
        &proved.dlog_plonk_index,
        Some(proved.stable_cycles),
    )
}

/// Proves a true width-2 (`N2`) recorded recursive step over two base proofs
/// of the same recorded circuit. `app_state_decimal` is the public state
/// bound by the N2 digest; the low-level adapter does not derive an
/// aggregation relation from the two previous states.
#[wasm_bindgen]
pub fn rust_pickles_prove_recorded_n2(
    circuit_json: String,
    first_witness_decimal: Vec<String>,
    second_witness_decimal: Vec<String>,
    app_state_decimal: Vec<String>,
) -> Result<String, JsError> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| JsError::new(&format!("invalid recorded circuit JSON: {err}")))?;
    let first_witness = parse_fp_decimals(first_witness_decimal, "first_witness")?;
    let second_witness = parse_fp_decimals(second_witness_decimal, "second_witness")?;
    let app_state = parse_fp_decimals(app_state_decimal, "app_state")?;
    let proved = crate::rayon::run_in_pool(|| {
        pickles::recorded::prove_recorded_n2(circuit, first_witness, second_witness, app_state)
    })
    .map_err(|err| JsError::new(&format!("rust pickles N2 prove failed: {err:?}")))?;
    recorded_n2_envelope(proved)
}

/// [`rust_pickles_verify_side_loaded`] with an explicit `dlog_plonk_index`
/// (the wrap VK commitments bound by the statement digest — the
/// `dlogPlonkIndex` of an N1 envelope), as JSON `[["x","y"], ...]`.
#[wasm_bindgen]
pub fn rust_pickles_verify_side_loaded_with_step_vk(
    app_state_decimal: Vec<String>,
    dlog_plonk_index_json: String,
    challenge_polynomial_commitments_json: String,
    old_bulletproof_challenges_json: String,
    proof_json: String,
) -> Result<bool, JsError> {
    let app_state = parse_fp_decimals(app_state_decimal, "app_state")?;
    let parse_points = |json: &str, name: &str| -> Result<Vec<(Fp, Fp)>, JsError> {
        serde_json::from_str::<Vec<(String, String)>>(json)
            .map_err(|err| JsError::new(&format!("invalid {name}: {err}")))?
            .iter()
            .map(|(x, y)| Ok((parse_fp_decimal(x, name)?, parse_fp_decimal(y, name)?)))
            .collect()
    };
    let dlog_index = parse_points(&dlog_plonk_index_json, "dlog_plonk_index")?;
    let commitments = parse_points(
        &challenge_polynomial_commitments_json,
        "challenge_polynomial_commitments",
    )?;
    let challenges = serde_json::from_str::<Vec<Vec<String>>>(&old_bulletproof_challenges_json)
        .map_err(|err| JsError::new(&format!("invalid old_bulletproof_challenges: {err}")))?
        .into_iter()
        .map(|vector| parse_fp_decimals(vector, "old_bulletproof_challenges"))
        .collect::<Result<Vec<_>, JsError>>()?;
    let proof = pickles::api::MinaWrapProof::from_o1js_json_string(&proof_json)
        .map_err(|err| JsError::new(&format!("invalid proof JSON: {err:?}")))?;
    let verified = crate::rayon::run_in_pool(|| {
        pickles::verify::verify_side_loaded_with_step_vk(
            &app_state,
            Some(&dlog_index),
            &commitments,
            &challenges,
            &proof,
        )
    });
    match verified {
        Ok(_) => Ok(true),
        Err(pickles::verify::StandaloneVerifyError::VerificationKey(err)) => Err(JsError::new(
            &format!("invalid side-loaded verification key: {err:?}"),
        )),
        Err(pickles::verify::StandaloneVerifyError::ProofDecoding) => {
            Err(JsError::new("invalid wrap wire proof"))
        }
        Err(_) => Ok(false),
    }
}

/// A kept base-case proof: an opaque handle whose full native proof stays in
/// WASM memory so `rust_pickles_prove_recorded_n1_over` can recursively
/// verify it (the ZkProgram `SelfProof` shape).
#[wasm_bindgen]
pub struct WasmRecordedBaseHandle(pickles::recorded::RecordedBaseHandle);

/// Opaque reusable Step/Wrap prover indexes for one recorded base circuit.
#[wasm_bindgen]
pub struct WasmRecordedCompiledBase(pickles::recorded::RecordedCompiledBase);

#[wasm_bindgen]
pub struct WasmRecordedCompiledN1(pickles::recorded::RecordedCompiledN1);

#[wasm_bindgen]
pub fn rust_pickles_recorded_base_cache_key(circuit_json: String) -> Result<String, JsError> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| JsError::new(&format!("invalid recorded circuit JSON: {err}")))?;
    Ok(pickles::recorded::RecordedCompiledBase::cache_key(&circuit))
}

#[wasm_bindgen]
pub fn rust_pickles_recorded_base_cache_bytes(
    compiled: &WasmRecordedCompiledBase,
) -> Result<Vec<u8>, JsError> {
    compiled
        .0
        .to_cache_bytes()
        .map_err(|err| JsError::new(&format!("failed to serialize Rust Pickles cache: {err}")))
}

#[wasm_bindgen]
pub fn rust_pickles_compile_recorded_base_from_cache_bytes(
    circuit_json: String,
    witness_bytes: &[u8],
    cache_bytes: &[u8],
) -> Result<WasmRecordedCompiledBase, JsError> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| JsError::new(&format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_bytes(witness_bytes, "witness")?;
    let compiled = crate::rayon::run_in_pool(|| {
        pickles::recorded::RecordedCompiledBase::from_cache_bytes(circuit, witness, cache_bytes)
    })
    .map_err(|err| JsError::new(&format!("invalid Rust Pickles cache: {err}")))?;
    Ok(WasmRecordedCompiledBase(compiled))
}

#[wasm_bindgen]
pub fn rust_pickles_compile_recorded_base(
    circuit_json: String,
    witness_decimal: Vec<String>,
) -> Result<WasmRecordedCompiledBase, JsError> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| JsError::new(&format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_decimals(witness_decimal, "witness")?;
    let compiled = crate::rayon::run_in_pool(|| {
        pickles::recorded::RecordedCompiledBase::compile(circuit, witness)
    })
    .map_err(|err| JsError::new(&format!("rust pickles compile failed: {err:?}")))?;
    Ok(WasmRecordedCompiledBase(compiled))
}

#[wasm_bindgen]
pub fn rust_pickles_compile_recorded_base_bytes(
    circuit_json: String,
    witness_bytes: &[u8],
) -> Result<WasmRecordedCompiledBase, JsError> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| JsError::new(&format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_bytes(witness_bytes, "witness")?;
    let compiled = crate::rayon::run_in_pool(|| {
        pickles::recorded::RecordedCompiledBase::compile(circuit, witness)
    })
    .map_err(|err| JsError::new(&format!("rust pickles compile failed: {err:?}")))?;
    Ok(WasmRecordedCompiledBase(compiled))
}

#[wasm_bindgen]
pub fn rust_pickles_prove_recorded_base_keep_compiled(
    compiled: &mut WasmRecordedCompiledBase,
    witness_decimal: Vec<String>,
) -> Result<WasmRecordedBaseHandle, JsError> {
    let witness = parse_fp_decimals(witness_decimal, "witness")?;
    let handle = crate::rayon::run_in_pool(|| compiled.0.prove_keep(witness))
        .map_err(|err| JsError::new(&format!("rust pickles prove failed: {err:?}")))?;
    Ok(WasmRecordedBaseHandle(handle))
}

#[wasm_bindgen]
pub fn rust_pickles_prove_recorded_base_keep_compiled_bytes(
    compiled: &mut WasmRecordedCompiledBase,
    witness_bytes: &[u8],
) -> Result<WasmRecordedBaseHandle, JsError> {
    let witness = parse_fp_bytes(witness_bytes, "witness")?;
    let handle = crate::rayon::run_in_pool(|| compiled.0.prove_keep(witness))
        .map_err(|err| JsError::new(&format!("rust pickles prove failed: {err:?}")))?;
    Ok(WasmRecordedBaseHandle(handle))
}

#[wasm_bindgen]
pub fn rust_pickles_compile_recorded_n1(
    previous: &WasmRecordedBaseHandle,
    circuit_json: String,
    witness_decimal: Vec<String>,
) -> Result<WasmRecordedCompiledN1, JsError> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| JsError::new(&format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_decimals(witness_decimal, "witness")?;
    pickles::set_compile_profile_hook(Some(log_pickles_compile_profile));
    let compiled = crate::rayon::run_in_pool(|| {
        pickles::recorded::RecordedCompiledN1::compile(&previous.0, circuit, witness)
    });
    pickles::set_compile_profile_hook(None);
    let compiled = compiled
        .map_err(|err| JsError::new(&format!("rust pickles N1 compile failed: {err:?}")))?;
    Ok(WasmRecordedCompiledN1(compiled))
}

#[wasm_bindgen]
pub fn rust_pickles_compile_recorded_n1_bytes(
    previous: &WasmRecordedBaseHandle,
    circuit_json: String,
    witness_bytes: &[u8],
) -> Result<WasmRecordedCompiledN1, JsError> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| JsError::new(&format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_bytes(witness_bytes, "witness")?;
    pickles::set_compile_profile_hook(Some(log_pickles_compile_profile));
    let compiled = crate::rayon::run_in_pool(|| {
        pickles::recorded::RecordedCompiledN1::compile(&previous.0, circuit, witness)
    });
    pickles::set_compile_profile_hook(None);
    let compiled = compiled
        .map_err(|err| JsError::new(&format!("rust pickles N1 compile failed: {err:?}")))?;
    Ok(WasmRecordedCompiledN1(compiled))
}

fn log_pickles_compile_profile(profile: pickles::CompileProfile) {
    crate::console_log(&format!(
        "Rust Pickles compile profile: lowering={:.1}ms cs={:.1}ms lagrange={:.1}ms index={:.1}ms",
        profile.lowering_micros as f64 / 1000.0,
        profile.constraint_system_micros as f64 / 1000.0,
        profile.lagrange_micros as f64 / 1000.0,
        profile.prover_index_micros as f64 / 1000.0,
    ));
}

#[wasm_bindgen]
pub fn rust_pickles_prove_recorded_n1_compiled(
    compiled: &mut WasmRecordedCompiledN1,
    previous: &WasmRecordedBaseHandle,
    witness_decimal: Vec<String>,
) -> Result<String, JsError> {
    let witness = parse_fp_decimals(witness_decimal, "witness")?;
    let handle = crate::rayon::run_in_pool(|| compiled.0.prove_keep(&previous.0, witness))
        .map_err(|err| JsError::new(&format!("rust pickles N1 prove failed: {err:?}")))?;
    let proved = handle
        .to_recorded_n1_proof()
        .ok_or_else(|| JsError::new("compiled N1 did not return a recursive proof"))?;
    recorded_n1_envelope(
        &proved.app_state,
        &proved.proof,
        &proved.challenge_polynomial_commitment,
        &proved.old_bulletproof_challenges,
        &proved.dlog_plonk_index,
        None,
    )
}

#[wasm_bindgen]
pub fn rust_pickles_prove_recorded_n1_compiled_bytes(
    compiled: &mut WasmRecordedCompiledN1,
    previous: &WasmRecordedBaseHandle,
    witness_bytes: &[u8],
) -> Result<String, JsError> {
    let witness = parse_fp_bytes(witness_bytes, "witness")?;
    let handle = crate::rayon::run_in_pool(|| compiled.0.prove_keep(&previous.0, witness))
        .map_err(|err| JsError::new(&format!("rust pickles N1 prove failed: {err:?}")))?;
    let proved = handle
        .to_recorded_n1_proof()
        .ok_or_else(|| JsError::new("compiled N1 did not return a recursive proof"))?;
    recorded_n1_envelope(
        &proved.app_state,
        &proved.proof,
        &proved.challenge_polynomial_commitment,
        &proved.old_bulletproof_challenges,
        &proved.dlog_plonk_index,
        None,
    )
}

/// `rust_pickles_prove_recorded_base`, but keeps the full base proof alive
/// for chaining. Read its `{ appState, proof }` envelope with
/// `rust_pickles_recorded_base_envelope`.
#[wasm_bindgen]
pub fn rust_pickles_prove_recorded_base_keep(
    circuit_json: String,
    witness_decimal: Vec<String>,
) -> Result<WasmRecordedBaseHandle, JsError> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| JsError::new(&format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_decimals(witness_decimal, "witness")?;
    let handle = crate::rayon::run_in_pool(|| {
        pickles::recorded::prove_recorded_base_case_keep(circuit, witness)
    })
    .map_err(|err| JsError::new(&format!("rust pickles prove failed: {err:?}")))?;
    Ok(WasmRecordedBaseHandle(handle))
}

/// The `{ appState, proof }` envelope of a kept base proof.
#[wasm_bindgen]
pub fn rust_pickles_recorded_base_envelope(
    handle: &WasmRecordedBaseHandle,
) -> Result<String, JsError> {
    let proved = handle.0.to_recorded_proof();
    let envelope = serde_json::json!({
        "appState": proved
            .app_state
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        "proof": proved.proof.to_o1js_json_value(),
    });
    serde_json::to_string(&envelope)
        .map_err(|err| JsError::new(&format!("envelope encoding failed: {err}")))
}

/// Proves one recursive (N1) Pickles cycle whose step runs a new recorded
/// circuit while verifying the kept base proof. Same envelope as
/// `rust_pickles_prove_recorded_n1`; the digest binds the new `appState`.
#[wasm_bindgen]
pub fn rust_pickles_prove_recorded_n1_over(
    handle: &WasmRecordedBaseHandle,
    circuit_json: String,
    witness_decimal: Vec<String>,
) -> Result<String, JsError> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| JsError::new(&format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_decimals(witness_decimal, "witness")?;
    let proved = crate::rayon::run_in_pool(|| {
        pickles::recorded::prove_recorded_n1_over(&handle.0, circuit, witness)
    })
    .map_err(|err| JsError::new(&format!("rust pickles N1-over prove failed: {err:?}")))?;
    recorded_n1_envelope(
        &proved.app_state,
        &proved.proof,
        &proved.challenge_polynomial_commitment,
        &proved.old_bulletproof_challenges,
        &proved.dlog_plonk_index,
        None,
    )
}
