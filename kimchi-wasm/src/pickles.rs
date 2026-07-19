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
pub struct WasmRecordedCompiledN2(pickles::recorded::RecordedCompiledN2);

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
    console_error_panic_hook::set_once();
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
    console_error_panic_hook::set_once();
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

/// Assembles the compile-time proof template as a proof-SHAPED donor from
/// the compiled base indexes — no prover runs during compilation (the donor
/// is proven index-equivalent to a real base proof in pickles).
#[wasm_bindgen]
pub fn rust_pickles_recorded_base_donor_handle_bytes(
    compiled: &WasmRecordedCompiledBase,
    witness_bytes: &[u8],
) -> Result<WasmRecordedBaseHandle, JsError> {
    let witness = parse_fp_bytes(witness_bytes, "witness")?;
    let handle = crate::rayon::run_in_pool(|| compiled.0.donor_handle(&witness))
        .map_err(|err| JsError::new(&format!("rust pickles donor template failed: {err:?}")))?;
    Ok(WasmRecordedBaseHandle(handle))
}

/// Canonical Mina side-loaded VK of a compiled base circuit:
/// `{"base64": ..., "hash": ...}` — the same data/hash pair jsoo's
/// `Program.compile()` returns.
#[wasm_bindgen]
pub fn rust_pickles_recorded_base_vk_envelope(
    compiled: &WasmRecordedCompiledBase,
) -> Result<String, JsError> {
    let (base64, hash) = compiled
        .0
        .verification_key_envelope()
        .map_err(|err| JsError::new(&format!("VK envelope failed: {err:?}")))?;
    serde_json::to_string(&serde_json::json!({ "base64": base64, "hash": hash }))
        .map_err(|err| JsError::new(&format!("envelope encoding failed: {err}")))
}

/// Seeds the in-memory Lagrange-basis cache from an o1js `Cache` entry
/// payload (`lagrange-basis-{f}-{domain}`, jsoo JSON format — the identical
/// entries jsoo reads and writes). wasm has no filesystem: the JS host reads
/// the cache through its `Cache` object and passes the bytes in. Returns
/// false on any mismatch (the basis is then recomputed on demand).
#[wasm_bindgen]
pub fn rust_pickles_seed_lagrange_basis(curve: String, domain_log2: u32, bytes: &[u8]) -> bool {
    pickles::common::seed_lagrange_basis_jsoo(&curve, domain_log2, bytes)
}

/// Seeds the process-global SRS from an o1js `Cache` entry payload
/// (`srs-fp-65536` / `srs-fq-32768`, jsoo `[h, ...g]` JSON — the identical
/// entries jsoo reads and writes) — MUST run before any Lagrange seeding or
/// compile (those create the SRS if absent, which is the expensive serial
/// group map in wasm).
#[wasm_bindgen]
pub fn rust_pickles_seed_srs(curve: String, bytes: &[u8]) -> bool {
    match curve.as_str() {
        "vesta" => pickles::common::seed_tick_srs_jsoo(bytes),
        "pallas" => pickles::common::seed_tock_srs_jsoo(bytes),
        _ => false,
    }
}

/// Lazy-carry probe (bench mode 6): Montgomery multiplication for pasta
/// Fp in NINE 29-BIT LIMBS. Products are < 2^58, so a u64 column can
/// absorb the whole multiplication's 18 products WITHOUT propagating
/// carries — the inner loop has no dependency chain (the 32-bit CIOS
/// spends most of its time waiting on serial carries). One carry per
/// round, one propagation pass at the end. This is the ZPRIZE-style
/// design; the probe measures the kernel before any integration debate.
#[cfg(target_arch = "wasm32")]
mod lazy29_probe {
    /// Pasta Fp modulus in 29-bit little-endian limbs.
    pub const P29: [u64; 9] = [
        0x1, 0x9698768, 0x133e46e6, 0xd31f812, 0x224, 0, 0, 0, 0x400000,
    ];
    /// -p^{-1} mod 2^29.
    const INV29: u64 = 0x1fff_ffff;
    const MASK29: u64 = (1 << 29) - 1;

    /// `a * b * 2^-261 mod p`, limbs < 2^29 in, limbs < 2^29 out.
    #[inline(always)]
    pub fn mont_mul(a: &[u64; 9], b: &[u64; 9]) -> [u64; 9] {
        let mut t = [0u64; 9];
        for i in 0..9 {
            let ai = a[i];
            // Column 0 of this round: resolve m and its exact carry.
            let t0 = t[0] + ai * b[0];
            let m = ((t0 & MASK29) * INV29) & MASK29;
            let c = (t0 + m * P29[0]) >> 29;
            // Everything else: TWO mul-adds per column, no carries.
            t[0] = t[1] + ai * b[1] + m * P29[1] + c;
            t[1] = t[2] + ai * b[2] + m * P29[2];
            t[2] = t[3] + ai * b[3] + m * P29[3];
            t[3] = t[4] + ai * b[4] + m * P29[4];
            t[4] = t[5] + ai * b[5] + m * P29[5];
            t[5] = t[6] + ai * b[6] + m * P29[6];
            t[6] = t[7] + ai * b[7] + m * P29[7];
            t[7] = t[8] + ai * b[8] + m * P29[8];
            t[8] = 0;
        }
        // Single deferred carry propagation.
        let mut out = [0u64; 9];
        let mut carry = 0u64;
        for j in 0..9 {
            let v = t[j] + carry;
            out[j] = v & MASK29;
            carry = v >> 29;
        }
        debug_assert_eq!(carry, 0);
        // The lazy bound leaves out < few*p: subtract until < p.
        while ge(&out, &P29) {
            let mut borrow = 0i64;
            for j in 0..9 {
                let v = out[j] as i64 - P29[j] as i64 + borrow;
                out[j] = (v & MASK29 as i64) as u64;
                borrow = v >> 63;
            }
        }
        out
    }

    fn ge(a: &[u64; 9], p: &[u64; 9]) -> bool {
        for j in (0..9).rev() {
            if a[j] != p[j] {
                return a[j] > p[j];
            }
        }
        true
    }

    /// 256-bit little-endian u64 limbs -> nine 29-bit limbs.
    pub fn from_u64x4(l: &[u64; 4]) -> [u64; 9] {
        let mut out = [0u64; 9];
        for j in 0..9 {
            let bit = 29 * j;
            let (w, off) = (bit / 64, bit % 64);
            let mut v = l[w] >> off;
            if off > 35 && w + 1 < 4 {
                v |= l[w + 1] << (64 - off);
            }
            out[j] = v & MASK29;
        }
        out
    }

    /// Nine 29-bit limbs -> 256-bit little-endian u64 limbs.
    pub fn to_u64x4(l: &[u64; 9]) -> [u64; 4] {
        let mut out = [0u64; 4];
        for j in 0..9 {
            let bit = 29 * j;
            let (w, off) = (bit / 64, bit % 64);
            out[w] |= l[j] << off;
            if off > 35 && w + 1 < 4 {
                out[w + 1] |= l[j] >> (64 - off);
            }
        }
        out
    }
}

/// Lazy29 FFT probe (bench modes 8/9): a complete radix-2 DIT FFT whose
/// butterflies run in the lazy-carry 29-bit domain (`ark_ff::lazy29`),
/// data converted at the boundaries — measured against ark-poly's FFT on
/// the same input. Twiddles are converted once (cached per domain in a
/// real integration). Self-checked element-wise against ark's result.
#[cfg(target_arch = "wasm32")]
mod lazy_fft_probe {
    use ark_ff::lazy29;
    use mina_curves::pasta::fields::FqConfig;

    pub type L = [u64; lazy29::LIMBS];

    fn bit_reverse(a: &mut [L]) {
        let n = a.len();
        let bits = n.trailing_zeros();
        for i in 0..n {
            let j = ((i as u32).reverse_bits() >> (32 - bits)) as usize;
            if j > i {
                a.swap(i, j);
            }
        }
    }

    /// Stage twiddles for a size-n FFT: `tw[s][j] = (omega^(n/2^(s+1)))^j`.
    pub fn twiddles(omega: mina_curves::pasta::Fp, n: usize, entry: &L) -> Vec<Vec<L>> {
        use ark_ff::Field as _;
        let stages = n.trailing_zeros() as usize;
        let mut out = Vec::with_capacity(stages);
        for s in 0..stages {
            let len = 1usize << (s + 1);
            let w = omega.pow([(n / len) as u64]);
            let mut acc = mina_curves::pasta::Fp::ONE;
            let mut tws = Vec::with_capacity(len / 2);
            for _ in 0..len / 2 {
                tws.push(lazy29::enter::<FqConfig>(&acc.0, entry));
                acc *= w;
            }
            out.push(tws);
        }
        out
    }

    /// In-place natural-order DIT radix-2 FFT, all arithmetic lazy29.
    pub fn fft_in_place(a: &mut [L], twiddles: &[Vec<L>]) {
        bit_reverse(a);
        let n = a.len();
        let (mut len, mut stage) = (2usize, 0usize);
        while len <= n {
            let tw = &twiddles[stage];
            for block in a.chunks_mut(len) {
                let (lo, hi) = block.split_at_mut(len / 2);
                for j in 0..len / 2 {
                    let t = lazy29::mont_mul::<FqConfig>(&hi[j], &tw[j]);
                    let u = lo[j];
                    lo[j] = lazy29::add::<FqConfig>(&u, &t);
                    hi[j] = lazy29::sub::<FqConfig>(&u, &t);
                }
            }
            len <<= 1;
            stage += 1;
        }
    }
}

/// Runtime switch for the wasm batched-affine MSM dispatch (one-build
/// A/B measurement + production kill-switch, like the lazy-FFT one).
#[wasm_bindgen]
pub fn rust_pickles_set_batch_affine_msm(enabled: bool) {
    ark_ec::scalar_mul::variable_base::batch_affine::set_wasm_batch_affine_msm(enabled);
}

/// Kernel census: counters incremented inside the hot kernels (patched
/// ark fork: MSM calls/points and FFT calls/sizes; mina-poseidon:
/// permutations). Read after a real compile/prove to map where the
/// multiplications go. `reset` zeroes the counters after reading.
#[wasm_bindgen]
pub fn rust_pickles_kernel_census(reset: bool) -> String {
    use ark_ec::scalar_mul::variable_base::wasm_stats as msm;
    use ark_poly::domain::radix2::wasm_stats as fft;
    use core::sync::atomic::Ordering::Relaxed;
    use mina_poseidon::permutation::wasm_stats as pos;
    let out = format!(
        "{{\"poseidon_permutations\":{},\"msm_calls\":{},\"msm_points\":{},\"msm_calls_big\":{},\"msm_points_big\":{},\"fft_calls\":{},\"fft_elems\":{},\"fft_work\":{}}}",
        pos::PERMUTATIONS.load(Relaxed),
        msm::MSM_CALLS.load(Relaxed),
        msm::MSM_POINTS.load(Relaxed),
        msm::MSM_CALLS_BIG.load(Relaxed),
        msm::MSM_POINTS_BIG.load(Relaxed),
        fft::FFT_CALLS.load(Relaxed),
        fft::FFT_ELEMS.load(Relaxed),
        fft::FFT_WORK.load(Relaxed),
    );
    if reset {
        for c in [
            &pos::PERMUTATIONS,
            &msm::MSM_CALLS,
            &msm::MSM_POINTS,
            &msm::MSM_CALLS_BIG,
            &msm::MSM_POINTS_BIG,
            &fft::FFT_CALLS,
            &fft::FFT_ELEMS,
            &fft::FFT_WORK,
        ] {
            c.store(0, Relaxed);
        }
    }
    out
}

/// Runtime switch for the ark-poly wasm lazy-carry FFT dispatch
/// (measurement harnesses compare both paths in one build; also a
/// production kill-switch).
#[wasm_bindgen]
pub fn rust_pickles_set_lazy_fft(enabled: bool) {
    ark_poly::domain::radix2::set_wasm_lazy_fft(enabled);
}

/// Micro-bench of raw field-multiplication cost inside this wasm module.
/// Returns milliseconds for `iters` multiplications: `mode = 0` chains
/// dependent multiplications (latency), `mode = 1` runs 4 independent
/// accumulators (throughput — the headroom SIMD 2-lane batching can tap).
/// Bench-protocol tool (BENCHMARKS.md): isolates the field backend from
/// MSM/FFT/allocator effects.
#[wasm_bindgen]
pub fn rust_pickles_bench_field_mul(iters: u32, mode: u32) -> f64 {
    use ark_ff::{Field as _, One as _, Zero as _};
    use mina_curves::pasta::Fp;
    let y = Fp::from(0x9e3779b97f4a7c15u64);
    let t0 = js_sys::Date::now();
    let sink = match mode {
        0 => {
            let mut x = Fp::one() + y;
            for _ in 0..iters {
                x *= y;
            }
            x
        }
        6 => {
            use lazy29_probe as lz;
            // Enter the 2^261 Montgomery domain through ark itself:
            // x29 = to29(raw(x * R261)); then mont_mul stays in-domain and
            // raw results compare against ark's field multiplication.
            let r261 = Fp::from(2u64).pow([261u64]);
            use ark_ff::PrimeField as _;
            let enter = |v: Fp| lz::from_u64x4(&(v * r261).into_bigint().0);
            let mut x = Fp::one() + y;
            let mut x29 = enter(x);
            let y29 = enter(y);
            for step in 0..256 {
                let expected = x * y;
                let got = lz::mont_mul(&x29, &y29);
                if lz::to_u64x4(&got) != (expected * r261).into_bigint().0 {
                    return -2.0 - step as f64;
                }
                x = expected;
                x29 = got;
            }
            let y29 = core::hint::black_box(y29);
            let t0 = js_sys::Date::now();
            for _ in 0..iters {
                x29 = lz::mont_mul(&core::hint::black_box(x29), &y29);
            }
            let elapsed = js_sys::Date::now() - t0;
            if lz::to_u64x4(&core::hint::black_box(x29)) == [0u64; 4] {
                return -1.0;
            }
            return elapsed;
        }
        7 => {
            use lazy29_probe as lz;
            let r261 = Fp::from(2u64).pow([261u64]);
            use ark_ff::PrimeField as _;
            let enter = |v: Fp| lz::from_u64x4(&(v * r261).into_bigint().0);
            let y29 = core::hint::black_box(enter(y));
            let mut a = core::hint::black_box(enter(Fp::one() + y));
            let mut b = core::hint::black_box(enter(y + y));
            let mut c = core::hint::black_box(enter(y * y));
            let mut d = core::hint::black_box(enter(y * y + y));
            let t0 = js_sys::Date::now();
            for _ in 0..iters / 4 {
                a = lz::mont_mul(&a, &y29);
                b = lz::mont_mul(&b, &y29);
                c = lz::mont_mul(&c, &y29);
                d = lz::mont_mul(&d, &y29);
            }
            let elapsed = js_sys::Date::now() - t0;
            let sink = core::hint::black_box((a, b, c, d));
            if lz::to_u64x4(&sink.0) == [0u64; 4] {
                return -1.0;
            }
            return elapsed;
        }
        // MSM baseline micro-bench: ark msm_bigint on Vesta (the SRS curve
        // for Fp circuits) with 2^iters pseudo-random points and scalars.
        // Returns ms per MSM (reps sized for ~1s total); self-checked at
        // size 64 against the naive sum.
        16 | 17 => {
            use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
            use ark_ff::AdditiveGroup as _;
            use ark_ff::PrimeField as _;
            use mina_curves::pasta::Vesta;
            let n = 1usize << iters.min(18);
            let mut acc = Vesta::generator().into_group();
            let step = acc.double();
            let mut proj = Vec::with_capacity(n);
            for _ in 0..n {
                proj.push(acc);
                acc += step;
                acc.double_in_place();
            }
            let bases = ark_ec::CurveGroup::normalize_batch(&proj);
            let mut sc = Fp::one() + y;
            let scalars: Vec<_> = (0..n)
                .map(|_| {
                    sc.square_in_place();
                    sc += y;
                    sc.into_bigint()
                })
                .collect();
            // Self-check on a small prefix.
            let m = 64.min(n);
            let want = bases[..m]
                .iter()
                .zip(&scalars[..m])
                .map(|(b, s)| b.mul_bigint(*s))
                .sum::<mina_curves::pasta::ProjectiveVesta>();
            use ark_ec::scalar_mul::variable_base::batch_affine::msm_bigint_batch_affine;
            use mina_curves::pasta::curves::vesta::VestaParameters;
            return crate::rayon::run_in_pool(|| {
                let got = if mode == 16 {
                    mina_curves::pasta::ProjectiveVesta::msm_bigint(&bases[..m], &scalars[..m])
                } else {
                    msm_bigint_batch_affine::<VestaParameters>(&bases[..m], &scalars[..m])
                };
                if got != want {
                    return -2.0;
                }
                let reps = ((1usize << 21) / n).max(1) as u32;
                let t0 = js_sys::Date::now();
                for _ in 0..reps {
                    let out = if mode == 16 {
                        mina_curves::pasta::ProjectiveVesta::msm_bigint(
                            core::hint::black_box(&bases),
                            core::hint::black_box(&scalars),
                        )
                    } else {
                        msm_bigint_batch_affine::<VestaParameters>(
                            core::hint::black_box(&bases),
                            core::hint::black_box(&scalars),
                        )
                    };
                    core::hint::black_box(out);
                }
                (js_sys::Date::now() - t0) / reps as f64
            });
        }
        // Poseidon permutation micro-bench (kimchi constants, pasta Fp):
        // ms total for `iters` permutations.
        15 => {
            use mina_poseidon::{
                constants::PlonkSpongeConstantsKimchi, pasta::FULL_ROUNDS,
                permutation::poseidon_block_cipher,
            };
            let params = mina_poseidon::pasta::fp_kimchi::static_params();
            let mut state = vec![Fp::one() + y, y, Fp::one()];
            let t0 = js_sys::Date::now();
            for _ in 0..iters {
                poseidon_block_cipher::<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>(
                    params,
                    core::hint::black_box(&mut state),
                );
            }
            let elapsed = js_sys::Date::now() - t0;
            if core::hint::black_box(&state)[0] == Fp::one() {
                return -1.0;
            }
            return elapsed;
        }
        // Fixed cost of one rayon parallel region in this pool (ms total
        // for `iters` empty regions).
        11 => {
            return crate::rayon::run_in_pool(|| {
                use rayon::prelude::*;
                if iters == 0 {
                    return rayon::current_num_threads() as f64;
                }
                (0..16usize).into_par_iter().for_each(|_| {});
                let t0 = js_sys::Date::now();
                for _ in 0..iters {
                    (0..16usize).into_par_iter().for_each(|i| {
                        core::hint::black_box(i);
                    });
                }
                js_sys::Date::now() - t0
            });
        }
        // 8/9 at 2^16 (tick domain), 13/14 the same pair at 2^12: the
        // integrated-vs-serial delta across sizes separates fixed overhead
        // from per-element cost.
        8 | 9 | 13 | 14 => {
            use ark_ff::lazy29;
            use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
            use lazy_fft_probe as lf;
            use mina_curves::pasta::fields::FqConfig;
            #[allow(non_snake_case)]
            let N: usize = if mode >= 13 { 1 << 12 } else { 1 << 16 };
            let domain = Radix2EvaluationDomain::<Fp>::new(N).unwrap();
            // Varied input via a squaring chain.
            let mut coeffs = Vec::with_capacity(N);
            let mut x = Fp::one() + y;
            for _ in 0..N {
                x.square_in_place();
                x += y;
                coeffs.push(x);
            }
            let entry = lazy29::entry_constant::<FqConfig>();
            let tw = lf::twiddles(domain.group_gen, N, &entry);
            // Self-check: lazy FFT == ark FFT, element-wise. ark-poly is
            // built with the parallel feature: its FFT must run inside the
            // worker pool (that is also the production configuration).
            let expected = crate::rayon::run_in_pool(|| domain.fft(&coeffs));
            let mut d: Vec<lf::L> = coeffs
                .iter()
                .map(|c| lazy29::enter::<FqConfig>(&c.0, &entry))
                .collect();
            lf::fft_in_place(&mut d, &tw);
            for (i, (got, want)) in d.iter().zip(&expected).enumerate() {
                if lazy29::exit::<FqConfig>(got) != (want.0) {
                    return -2.0 - i as f64;
                }
            }
            let reps = iters.max(1);
            return crate::rayon::run_in_pool(|| {
                let t0 = js_sys::Date::now();
                if mode == 8 || mode == 13 {
                    for _ in 0..reps {
                        let out = domain.fft(core::hint::black_box(&coeffs));
                        core::hint::black_box(out);
                    }
                } else {
                    for _ in 0..reps {
                        let mut d: Vec<lf::L> = core::hint::black_box(&coeffs)
                            .iter()
                            .map(|c| lazy29::enter::<FqConfig>(&c.0, &entry))
                            .collect();
                        lf::fft_in_place(&mut d, &tw);
                        let out: Vec<_> = d.iter().map(lazy29::exit::<FqConfig>).collect();
                        core::hint::black_box(out);
                    }
                }
                js_sys::Date::now() - t0
            });
        }
        _ => {
            let mut a = Fp::one() + y;
            let mut b = a + y;
            let mut c = b + y;
            let mut d = c + y;
            for _ in 0..iters / 4 {
                a *= y;
                b *= y;
                c *= y;
                d *= y;
            }
            a + b + c + d
        }
    };
    let elapsed = js_sys::Date::now() - t0;
    // A field element is never zero after multiplying nonzero values —
    // this keeps the loop out of reach of dead-code elimination.
    if sink.is_zero() {
        return -1.0;
    }
    elapsed
}

/// Seeds every SRS/Lagrange cache entry in ONE wasm call: entering the
/// rayon pool costs ~200ms of worker coordination per call, so the per-entry
/// bindings above are only a fallback. `entries_json` is
/// `[{"curve": "vesta"|"pallas", "domainLog2": -1|n}, ...]` aligned with
/// `payloads` (jsoo JSON bytes); SRS entries (`domainLog2 = -1`) must come
/// first, exactly like the per-entry protocol. Returns the number of entries
/// accepted (a malformed payload just means recomputation).
#[wasm_bindgen]
pub fn rust_pickles_seed_srs_cache_batch(
    entries_json: String,
    payloads: js_sys::Array,
) -> Result<u32, JsError> {
    #[derive(serde::Deserialize)]
    struct Entry {
        curve: String,
        #[serde(rename = "domainLog2")]
        domain_log2: i32,
    }
    let entries: Vec<Entry> = serde_json::from_str(&entries_json)
        .map_err(|err| JsError::new(&format!("invalid seed entries JSON: {err}")))?;
    if entries.len() != payloads.length() as usize {
        return Err(JsError::new("seed entries/payloads length mismatch"));
    }
    let payloads: Vec<Vec<u8>> = payloads
        .iter()
        .map(|value| js_sys::Uint8Array::new(&value).to_vec())
        .collect();
    Ok(crate::rayon::run_in_pool(move || {
        let mut seeded = 0u32;
        for (entry, bytes) in entries.iter().zip(&payloads) {
            let ok = if entry.domain_log2 < 0 {
                match entry.curve.as_str() {
                    "vesta" => pickles::common::seed_tick_srs_jsoo(bytes),
                    "pallas" => pickles::common::seed_tock_srs_jsoo(bytes),
                    _ => false,
                }
            } else {
                pickles::common::seed_lagrange_basis_jsoo(
                    &entry.curve,
                    entry.domain_log2 as u32,
                    bytes,
                )
            };
            if ok {
                seeded += 1;
            }
        }
        seeded
    }))
}

/// Exports the process-global SRS as the jsoo cache payload for the JS host
/// to persist through its `Cache` object (empty when the SRS has not been
/// created yet).
#[wasm_bindgen]
pub fn rust_pickles_export_srs(curve: String) -> Vec<u8> {
    match curve.as_str() {
        "vesta" => pickles::common::export_tick_srs_jsoo().unwrap_or_default(),
        "pallas" => pickles::common::export_tock_srs_jsoo().unwrap_or_default(),
        _ => Vec::new(),
    }
}

/// Exports a computed Lagrange basis as the jsoo cache payload, so the JS
/// host can persist it through its `Cache` object. Returns an empty vector
/// if the basis is not (yet) in the in-memory cache.
#[wasm_bindgen]
pub fn rust_pickles_export_lagrange_basis(curve: String, domain_log2: u32) -> Vec<u8> {
    pickles::common::export_lagrange_basis_jsoo(&curve, domain_log2).unwrap_or_default()
}

/// Compiles every method of a recorded program in one call, running the
/// per-branch compilations in PARALLEL inside the wasm rayon pool (the
/// per-method entries serialize across wasm calls). `branches_json` is
/// `[{"circuit": ..., "witness": ["dec", ...], "proofsVerified": 0|1|2}]`.
/// Returns a flat JS array of `[base, n1|null, n2|null]` triplets per branch.
#[wasm_bindgen]
pub fn rust_pickles_compile_recorded_program(
    branches_json: String,
) -> Result<js_sys::Array, JsError> {
    console_error_panic_hook::set_once();
    #[derive(serde::Deserialize)]
    struct Branch {
        circuit: pickles::recorded::RecordedCircuit,
        witness: Vec<String>,
        #[serde(rename = "proofsVerified")]
        proofs_verified: u8,
    }
    let branches: Vec<Branch> = serde_json::from_str(&branches_json)
        .map_err(|err| JsError::new(&format!("invalid program JSON: {err}")))?;
    let mut parsed = Vec::with_capacity(branches.len());
    for branch in branches {
        let witness = parse_fp_decimals(branch.witness, "witness")?;
        parsed.push((branch.circuit, witness, branch.proofs_verified));
    }
    type Compiled = (
        pickles::recorded::RecordedCompiledBase,
        Option<pickles::recorded::RecordedCompiledN1>,
        Option<pickles::recorded::RecordedCompiledN2>,
    );
    let compiled: Vec<Result<Compiled, String>> = crate::rayon::run_in_pool(|| {
        use rayon::prelude::*;
        parsed
            .into_par_iter()
            .map(|(circuit, witness, proofs_verified)| {
                let base = pickles::recorded::RecordedCompiledBase::compile(
                    circuit.clone(),
                    witness.clone(),
                )
                .map_err(|err| format!("base compile: {err:?}"))?;
                let template = (proofs_verified > 0)
                    .then(|| base.donor_handle(&witness))
                    .transpose()
                    .map_err(|err| format!("donor template: {err:?}"))?;
                let n1 = (proofs_verified == 1)
                    .then(|| {
                        pickles::recorded::RecordedCompiledN1::compile(
                            template.as_ref().expect("template"),
                            circuit.clone(),
                            witness.clone(),
                        )
                    })
                    .transpose()
                    .map_err(|err| format!("N1 compile: {err:?}"))?;
                let n2 = (proofs_verified == 2)
                    .then(|| {
                        pickles::recorded::RecordedCompiledN2::compile(
                            template.as_ref().expect("template"),
                            template.as_ref().expect("template"),
                            circuit,
                            witness,
                        )
                    })
                    .transpose()
                    .map_err(|err| format!("N2 compile: {err:?}"))?;
                Ok((base, n1, n2))
            })
            .collect()
    });
    let out = js_sys::Array::new();
    for entry in compiled {
        let (base, n1, n2) =
            entry.map_err(|err| JsError::new(&format!("program compile failed: {err}")))?;
        let triple = js_sys::Array::new();
        triple.push(&JsValue::from(WasmRecordedCompiledBase(base)));
        triple.push(&n1.map_or(JsValue::NULL, |n1| {
            JsValue::from(WasmRecordedCompiledN1(n1))
        }));
        triple.push(&n2.map_or(JsValue::NULL, |n2| {
            JsValue::from(WasmRecordedCompiledN2(n2))
        }));
        out.push(&triple);
    }
    Ok(out)
}

/// Drains the live-trace checkpoints — called by the tracer worker over the
/// shared memory while the main thread is blocked.
#[wasm_bindgen]
pub fn rust_pickles_debug_take_trace() -> String {
    kimchi::live_trace::take_recorded().join("\n")
}

fn live_trace_to_console(message: &str) {
    crate::console_log(message);
}

/// One compiled shared-wrap program (OCaml `Pickles.compile` shape): every
/// branch shares a single wrap index and canonical verification key.
#[wasm_bindgen]
pub struct WasmRecordedProgram(pickles::recorded::RecordedCompiledProgram);

/// Compiles a recorded program with ONE shared wrap circuit. Same input as
/// [`rust_pickles_compile_recorded_program`].
#[wasm_bindgen]
pub fn rust_pickles_compile_recorded_program_shared(
    branches_json: String,
) -> Result<WasmRecordedProgram, JsError> {
    console_error_panic_hook::set_once();
    #[derive(serde::Deserialize)]
    struct Branch {
        circuit: pickles::recorded::RecordedCircuit,
        witness: Vec<String>,
        #[serde(rename = "proofsVerified")]
        proofs_verified: u8,
    }
    let branches: Vec<Branch> = serde_json::from_str(&branches_json)
        .map_err(|err| JsError::new(&format!("invalid program JSON: {err}")))?;
    let mut parsed = Vec::with_capacity(branches.len());
    for branch in branches {
        let witness = parse_fp_decimals(branch.witness, "witness")?;
        parsed.push(pickles::recorded::RecordedProgramBranch {
            circuit: branch.circuit,
            witness,
            proofs_verified: branch.proofs_verified,
        });
    }
    let program =
        crate::rayon::run_in_pool(|| pickles::recorded::RecordedCompiledProgram::compile(parsed))
            .map_err(|err| JsError::new(&format!("program compile failed: {err:?}")))?;
    Ok(WasmRecordedProgram(program))
}

fn parse_program_branches(
    branches_json: &str,
) -> Result<Vec<pickles::recorded::RecordedProgramBranch>, JsError> {
    #[derive(serde::Deserialize)]
    struct Branch {
        circuit: pickles::recorded::RecordedCircuit,
        witness: Vec<String>,
        #[serde(rename = "proofsVerified")]
        proofs_verified: u8,
    }
    let branches: Vec<Branch> = serde_json::from_str(branches_json)
        .map_err(|err| JsError::new(&format!("invalid program JSON: {err}")))?;
    let mut parsed = Vec::with_capacity(branches.len());
    for branch in branches {
        let witness = parse_fp_decimals(branch.witness, "witness")?;
        parsed.push(pickles::recorded::RecordedProgramBranch {
            circuit: branch.circuit,
            witness,
            proofs_verified: branch.proofs_verified,
        });
    }
    Ok(parsed)
}

/// The prover-key cache id of a program (the o1js Cache persistentId).
#[wasm_bindgen]
pub fn rust_pickles_recorded_program_cache_key(branches_json: String) -> Result<String, JsError> {
    console_error_panic_hook::set_once();
    let parsed = parse_program_branches(&branches_json)?;
    Ok(pickles::recorded::RecordedCompiledProgram::cache_key(&parsed))
}

/// Serializes a compiled program's prover-key cache payload.
#[wasm_bindgen]
pub fn rust_pickles_recorded_program_cache_bytes(
    program: &WasmRecordedProgram,
) -> Result<Vec<u8>, JsError> {
    program
        .0
        .to_cache_bytes()
        .map_err(|err| JsError::new(&format!("program cache encode failed: {err}")))
}

/// Restores a compiled program from a prover-key cache payload (the jsoo
/// warm-compile shape: circuits re-synthesized, verifiers from the cache).
#[wasm_bindgen]
pub fn rust_pickles_compile_recorded_program_from_cache_bytes(
    branches_json: String,
    cache_bytes: Vec<u8>,
) -> Result<WasmRecordedProgram, JsError> {
    console_error_panic_hook::set_once();
    let parsed = parse_program_branches(&branches_json)?;
    let program = crate::rayon::run_in_pool(|| {
        pickles::recorded::RecordedCompiledProgram::from_cache_bytes(parsed, &cache_bytes)
    })
    .map_err(|err| JsError::new(&format!("program cache restore failed: {err:?}")))?;
    Ok(WasmRecordedProgram(program))
}

/// Debug bisection of the shared program compile: runs up to phase `stage`
/// and returns the accumulated timings. For locating wasm hangs.
#[wasm_bindgen]
pub fn rust_pickles_debug_program_stage(
    branches_json: String,
    stage: u32,
) -> Result<String, JsError> {
    console_error_panic_hook::set_once();
    #[derive(serde::Deserialize)]
    struct Branch {
        circuit: pickles::recorded::RecordedCircuit,
        witness: Vec<String>,
        #[serde(rename = "proofsVerified")]
        proofs_verified: u8,
    }
    let branches: Vec<Branch> = serde_json::from_str(&branches_json)
        .map_err(|err| JsError::new(&format!("invalid program JSON: {err}")))?;
    let mut parsed = Vec::with_capacity(branches.len());
    for branch in branches {
        let witness = parse_fp_decimals(branch.witness, "witness")?;
        parsed.push(pickles::recorded::RecordedProgramBranch {
            circuit: branch.circuit,
            witness,
            proofs_verified: branch.proofs_verified,
        });
    }
    crate::rayon::run_in_pool(|| {
        pickles::recorded::RecordedCompiledProgram::debug_compile_stage(parsed, stage as usize)
    })
    .map_err(|err| JsError::new(&format!("debug stage failed: {err:?}")))
}

/// Debug: probe sub-step isolation for one branch (see pickles
/// `debug_probe_branch`).
#[wasm_bindgen]
pub fn rust_pickles_debug_probe_branch(
    branches_json: String,
    branch_index: u32,
    mode: u32,
) -> Result<String, JsError> {
    console_error_panic_hook::set_once();
    #[derive(serde::Deserialize)]
    struct Branch {
        circuit: pickles::recorded::RecordedCircuit,
        witness: Vec<String>,
        #[serde(rename = "proofsVerified")]
        proofs_verified: u8,
    }
    let branches: Vec<Branch> = serde_json::from_str(&branches_json)
        .map_err(|err| JsError::new(&format!("invalid program JSON: {err}")))?;
    let mut parsed = Vec::with_capacity(branches.len());
    for branch in branches {
        let witness = parse_fp_decimals(branch.witness, "witness")?;
        parsed.push(pickles::recorded::RecordedProgramBranch {
            circuit: branch.circuit,
            witness,
            proofs_verified: branch.proofs_verified,
        });
    }
    crate::rayon::run_in_pool(|| {
        pickles::recorded::debug_probe_branch(parsed, branch_index as usize, mode)
    })
    .map_err(|err| JsError::new(&format!("probe debug failed: {err:?}")))
}

/// `{"base64": .., "hash": ..}` — the program's single canonical Mina
/// side-loaded verification key.
#[wasm_bindgen]
pub fn rust_pickles_recorded_program_vk_envelope(
    program: &WasmRecordedProgram,
) -> Result<String, JsError> {
    let (base64, hash) = program
        .0
        .verification_key_envelope()
        .map_err(|err| JsError::new(&format!("program VK envelope failed: {err:?}")))?;
    serde_json::to_string(&serde_json::json!({ "base64": base64, "hash": hash }))
        .map_err(|err| JsError::new(&format!("VK envelope encoding failed: {err}")))
}

#[wasm_bindgen]
pub fn rust_pickles_program_prove_n0_bytes(
    program: &mut WasmRecordedProgram,
    branch_index: u32,
    witness_bytes: &[u8],
) -> Result<WasmRecordedBaseHandle, JsError> {
    console_error_panic_hook::set_once();
    let witness = parse_fp_bytes(witness_bytes, "witness")?;
    let handle = crate::rayon::run_in_pool(|| program.0.prove_n0(branch_index as usize, witness))
        .map_err(|err| JsError::new(&format!("program N0 proving failed: {err:?}")))?;
    Ok(WasmRecordedBaseHandle(handle))
}

#[wasm_bindgen]
pub fn rust_pickles_program_prove_n1_bytes(
    program: &mut WasmRecordedProgram,
    branch_index: u32,
    previous: &WasmRecordedBaseHandle,
    witness_bytes: &[u8],
) -> Result<WasmRecordedBaseHandle, JsError> {
    console_error_panic_hook::set_once();
    kimchi::live_trace::set_hook(live_trace_to_console);
    kimchi::live_trace::checkpoint("wasm: n1 entry");
    let witness = parse_fp_bytes(witness_bytes, "witness")?;
    let handle = crate::rayon::run_in_pool(|| {
        program
            .0
            .prove_n1(branch_index as usize, &previous.0, witness)
    })
    .map_err(|err| JsError::new(&format!("program N1 proving failed: {err:?}")))?;
    Ok(WasmRecordedBaseHandle(handle))
}

#[wasm_bindgen]
pub fn rust_pickles_program_prove_n2_bytes(
    program: &mut WasmRecordedProgram,
    branch_index: u32,
    first: &WasmRecordedBaseHandle,
    second: &WasmRecordedBaseHandle,
    witness_bytes: &[u8],
) -> Result<WasmRecordedBaseHandle, JsError> {
    console_error_panic_hook::set_once();
    let witness = parse_fp_bytes(witness_bytes, "witness")?;
    let handle = crate::rayon::run_in_pool(|| {
        program
            .0
            .prove_n2(branch_index as usize, [&first.0, &second.0], witness)
    })
    .map_err(|err| JsError::new(&format!("program N2 proving failed: {err:?}")))?;
    Ok(WasmRecordedBaseHandle(handle))
}

/// Debug bisection of the program N1 prove (see pickles
/// `debug_prove_recursive_stage`).
#[wasm_bindgen]
pub fn rust_pickles_program_debug_prove_n1(
    program: &mut WasmRecordedProgram,
    branch_index: u32,
    previous: &WasmRecordedBaseHandle,
    witness_bytes: &[u8],
    stage: u32,
) -> Result<String, JsError> {
    console_error_panic_hook::set_once();
    let witness = parse_fp_bytes(witness_bytes, "witness")?;
    crate::rayon::run_in_pool(|| {
        program.0.debug_prove_recursive_stage(
            branch_index as usize,
            &[&previous.0],
            witness,
            stage as usize,
        )
    })
    .map_err(|err| JsError::new(&format!("prove debug failed: {err:?}")))
}

/// The N1-shaped recursive verification envelope of a program proof handle.
#[wasm_bindgen]
pub fn rust_pickles_recorded_program_n1_envelope(
    handle: &WasmRecordedBaseHandle,
) -> Result<String, JsError> {
    let (accumulators, challenges, dlog_plonk_index) = handle
        .0
        .program_verification_messages()
        .ok_or_else(|| JsError::new("proof handle is not a program proof"))?;
    let proved = handle.0.to_recorded_proof();
    let accumulator = accumulators
        .first()
        .ok_or_else(|| JsError::new("program proof carries no accumulator"))?;
    let old = challenges
        .first()
        .ok_or_else(|| JsError::new("program proof carries no challenges"))?;
    recorded_n1_envelope(
        &proved.app_state,
        &proved.proof,
        accumulator,
        old,
        &dlog_plonk_index,
        None,
    )
}

/// The N2-shaped recursive verification envelope of a program proof handle.
#[wasm_bindgen]
pub fn rust_pickles_recorded_program_n2_envelope(
    handle: &WasmRecordedBaseHandle,
) -> Result<String, JsError> {
    let (accumulators, challenges, dlog_plonk_index) = handle
        .0
        .program_verification_messages()
        .ok_or_else(|| JsError::new("proof handle is not a program proof"))?;
    if accumulators.len() != 2 || challenges.len() != 2 {
        return Err(JsError::new(
            "program proof does not carry two accumulators",
        ));
    }
    let proved = handle.0.to_recorded_proof();
    recorded_n2_envelope(pickles::recorded::RecordedN2Proof {
        app_state: proved.app_state,
        proof: proved.proof,
        challenge_polynomial_commitments: [accumulators[0], accumulators[1]],
        old_bulletproof_challenges: [challenges[0].clone(), challenges[1].clone()],
        dlog_plonk_index,
    })
}

#[wasm_bindgen]
pub fn rust_pickles_prove_recorded_n2_over_base_handles(
    first: &WasmRecordedBaseHandle,
    second: &WasmRecordedBaseHandle,
    circuit_json: String,
    witness_decimal: Vec<String>,
) -> Result<String, JsError> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| JsError::new(&format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_decimals(witness_decimal, "witness")?;
    let proved = crate::rayon::run_in_pool(|| {
        pickles::recorded::prove_recorded_n2_over_base_handles(
            &first.0, &second.0, circuit, witness,
        )
    })
    .map_err(|err| JsError::new(&format!("rust pickles N2 prove failed: {err:?}")))?;
    recorded_n2_envelope(proved)
}

#[wasm_bindgen]
pub fn rust_pickles_prove_recorded_n2_over_base_handles_bytes(
    first: &WasmRecordedBaseHandle,
    second: &WasmRecordedBaseHandle,
    circuit_json: String,
    witness_bytes: &[u8],
) -> Result<String, JsError> {
    let circuit: pickles::recorded::RecordedCircuit = serde_json::from_str(&circuit_json)
        .map_err(|err| JsError::new(&format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_bytes(witness_bytes, "witness")?;
    let proved = crate::rayon::run_in_pool(|| {
        pickles::recorded::prove_recorded_n2_over_base_handles(
            &first.0, &second.0, circuit, witness,
        )
    })
    .map_err(|err| JsError::new(&format!("rust pickles N2 prove failed: {err:?}")))?;
    recorded_n2_envelope(proved)
}

#[wasm_bindgen]
pub fn rust_pickles_compile_recorded_n2_bytes(
    first: &WasmRecordedBaseHandle,
    second: &WasmRecordedBaseHandle,
    circuit_json: String,
    witness_bytes: &[u8],
) -> Result<WasmRecordedCompiledN2, JsError> {
    let circuit = serde_json::from_str(&circuit_json)
        .map_err(|err| JsError::new(&format!("invalid recorded circuit JSON: {err}")))?;
    let witness = parse_fp_bytes(witness_bytes, "witness")?;
    let compiled = crate::rayon::run_in_pool(|| {
        pickles::recorded::RecordedCompiledN2::compile(&first.0, &second.0, circuit, witness)
    })
    .map_err(|err| JsError::new(&format!("rust pickles N2 compile failed: {err:?}")))?;
    Ok(WasmRecordedCompiledN2(compiled))
}

#[wasm_bindgen]
pub fn rust_pickles_prove_recorded_n2_compiled_bytes(
    compiled: &mut WasmRecordedCompiledN2,
    first: &WasmRecordedBaseHandle,
    second: &WasmRecordedBaseHandle,
    witness_bytes: &[u8],
) -> Result<String, JsError> {
    let witness = parse_fp_bytes(witness_bytes, "witness")?;
    let proved = crate::rayon::run_in_pool(|| compiled.0.prove(&first.0, &second.0, witness))
        .map_err(|err| JsError::new(&format!("rust pickles N2 prove failed: {err:?}")))?;
    recorded_n2_envelope(proved)
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

#[wasm_bindgen]
pub fn rust_pickles_prove_recorded_n1_compiled_keep(
    compiled: &mut WasmRecordedCompiledN1,
    previous: &WasmRecordedBaseHandle,
    witness_decimal: Vec<String>,
) -> Result<WasmRecordedBaseHandle, JsError> {
    let witness = parse_fp_decimals(witness_decimal, "witness")?;
    let handle = crate::rayon::run_in_pool(|| compiled.0.prove_keep(&previous.0, witness))
        .map_err(|err| JsError::new(&format!("rust pickles N1 prove failed: {err:?}")))?;
    Ok(WasmRecordedBaseHandle(handle))
}

#[wasm_bindgen]
pub fn rust_pickles_prove_recorded_n1_compiled_keep_bytes(
    compiled: &mut WasmRecordedCompiledN1,
    previous: &WasmRecordedBaseHandle,
    witness_bytes: &[u8],
) -> Result<WasmRecordedBaseHandle, JsError> {
    let witness = parse_fp_bytes(witness_bytes, "witness")?;
    let handle = crate::rayon::run_in_pool(|| compiled.0.prove_keep(&previous.0, witness))
        .map_err(|err| JsError::new(&format!("rust pickles N1 prove failed: {err:?}")))?;
    Ok(WasmRecordedBaseHandle(handle))
}

#[wasm_bindgen]
pub fn rust_pickles_recorded_n1_envelope(
    handle: &WasmRecordedBaseHandle,
) -> Result<String, JsError> {
    let proved = handle
        .0
        .to_recorded_n1_proof()
        .ok_or_else(|| JsError::new("proof handle is not recursive"))?;
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
