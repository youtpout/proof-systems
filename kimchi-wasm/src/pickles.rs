//! Pickles surface for JS: recorded-circuit base-case proving and standalone
//! side-loaded verification. Mirrors `kimchi-napi/src/pickles.rs` so o1js can
//! run the same flows in the browser (WASM) and in Node (NAPI).

use core::str::FromStr;

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
    let proved = pickles::recorded::prove_recorded_base_case(circuit, witness)
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
    let commitments = serde_json::from_str::<Vec<(String, String)>>(
        &challenge_polynomial_commitments_json,
    )
    .map_err(|err| JsError::new(&format!("invalid challenge_polynomial_commitments: {err}")))?
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
    match pickles::verify::verify_side_loaded(&app_state, &commitments, &challenges, &proof) {
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
    let proved = pickles::recorded::prove_recorded_n1(circuit, witness)
        .map_err(|err| JsError::new(&format!("rust pickles N1 prove failed: {err:?}")))?;
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
        .map_err(|err| JsError::new(&format!("envelope encoding failed: {err}")))
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
    match pickles::verify::verify_side_loaded_with_step_vk(
        &app_state,
        Some(&dlog_index),
        &commitments,
        &challenges,
        &proof,
    ) {
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
