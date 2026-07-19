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

/// Kernel census: Poseidon permutation counter (mina-poseidon) and the
/// prover phase wall-times (live_trace clock). Read after a real
/// compile/prove; `reset` zeroes the counters after reading.
#[wasm_bindgen]
pub fn rust_pickles_kernel_census(reset: bool) -> String {
    let phases = kimchi::live_trace::take_phase_times();
    let items: Vec<String> = phases
        .iter()
        .map(|(n, ms, c)| format!("\"{}\":[{:.1},{}]", n, ms, c))
        .collect();
    #[cfg(target_arch = "wasm32")]
    let permutations = {
        use core::sync::atomic::Ordering::Relaxed;
        use mina_poseidon::permutation::wasm_stats as pos;
        let count = pos::PERMUTATIONS.load(Relaxed);
        if reset {
            pos::PERMUTATIONS.store(0, Relaxed);
        }
        count
    };
    #[cfg(not(target_arch = "wasm32"))]
    let permutations = {
        let _ = reset;
        0u64
    };
    format!(
        "{{\"poseidon_permutations\":{},\"phases\":{{{}}}}}",
        permutations,
        items.join(","),
    )
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
        // MSM baseline micro-bench: ark msm_bigint on Vesta (the SRS curve
        // for Fp circuits) with 2^iters pseudo-random points and scalars.
        // Returns ms per MSM (reps sized for ~1s total); self-checked at
        // size 64 against the naive sum.
        16 => {
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
            return crate::rayon::run_in_pool(|| {
                let got = mina_curves::pasta::ProjectiveVesta::msm_bigint(&bases[..m], &scalars[..m]);
                if got != want {
                    return -2.0;
                }
                let reps = ((1usize << 21) / n).max(1) as u32;
                let t0 = js_sys::Date::now();
                for _ in 0..reps {
                    let out = mina_curves::pasta::ProjectiveVesta::msm_bigint(
                        core::hint::black_box(&bases),
                        core::hint::black_box(&scalars),
                    );
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
    // Compile branches sequentially: each branch's own compile already uses
    // the rayon pool internally (MSM/FFT/Lagrange), so iterating the branches
    // in parallel too nests parallelism on a bounded pool and deadlocks under
    // thread contention (reliably for 6+ mid-size branches, e.g. a token
    // contract). One branch at a time still saturates the pool per branch.
    let compiled: Vec<Result<Compiled, String>> = crate::rayon::run_in_pool(|| {
        parsed
            .into_iter()
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

/// Opt-in: routes live-trace phase checkpoints to the browser console.
/// Off by default so proving stays silent; call once from JS to re-enable
/// the kernel-census trace for a diagnostic run.
#[wasm_bindgen]
pub fn rust_pickles_debug_enable_console_trace() {
    kimchi::live_trace::set_hook(live_trace_to_console);
    kimchi::live_trace::set_clock(js_sys::Date::now);
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

/// The single canonical side-loaded VK of a NON-RECURSIVE program: one shared
/// width-0 wrap over every branch's Step verifier (OCaml `Pickles.compile`
/// shape for `max_proofs_verified = 0`), rather than one wrap per branch.
/// Returns `{ base64, hash }`.
#[wasm_bindgen]
pub fn rust_pickles_compile_recorded_program_base_shared_vk(
    branches_json: String,
) -> Result<String, JsError> {
    console_error_panic_hook::set_once();
    let branches = parse_program_branches(&branches_json)?;
    let (base64, hash) = crate::rayon::run_in_pool(|| {
        pickles::recorded::compile_recorded_program_base_shared_vk(branches)
    })
    .map_err(|err| JsError::new(&format!("shared base VK compile failed: {err:?}")))?;
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
