//! Coarse profiling of the recorded compile pipelines.
//! Run: PICKLES_PROFILE=1 cargo run -p pickles --release --example profile_compile [base|program]
use mina_curves::pasta::Fp;
use std::time::Instant;

fn tiny_circuit() -> pickles::recorded::RecordedCircuit {
    let json = r#"{
      "aux_count": 2,
      "output": [{"terms": [["1", 1]]}],
      "constraints": [
        {"kind": "square", "v": {"terms": [["1", 0]]}, "square": {"terms": [["1", 1]]}}
      ]
    }"#;
    serde_json::from_str(json).unwrap()
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "program".into());

    if mode == "dump" {
        // Dump the program circuits for an o1js branches JSON — the napi
        // `rust_pickles_recorded_program_circuits_json` path, but against
        // the LOCAL crate (gate-parity triage without an addon rebuild).
        let path = std::env::args().nth(2).expect("branches json path");
        #[derive(serde::Deserialize)]
        struct BranchJson {
            #[serde(rename = "proofsVerified")]
            proofs_verified: u8,
            circuit: pickles::recorded::RecordedCircuit,
        }
        let raw = std::fs::read_to_string(&path).expect("read branches json");
        let parsed: Vec<BranchJson> = serde_json::from_str(&raw).expect("parse branches json");
        let branches = parsed
            .into_iter()
            .map(|b| pickles::recorded::RecordedProgramBranch {
                witness: vec![Fp::from(0u64); b.circuit.aux_count as usize],
                circuit: b.circuit,
                proofs_verified: b.proofs_verified,
            })
            .collect();
        let json =
            pickles::recorded::dump_recorded_program_circuits(branches).expect("dump circuits");
        let out = std::env::args()
            .nth(3)
            .unwrap_or_else(|| "/tmp/claude-1000/local-gates-rust.json".into());
        std::fs::write(&out, json).expect("write dump");
        eprintln!("dumped to {out}");
        return;
    }

    if mode == "wrap-labels" {
        let branches = vec![
            pickles::recorded::RecordedProgramBranch {
                circuit: tiny_circuit(),
                witness: vec![Fp::from(6u64), Fp::from(36u64)],
                proofs_verified: 0,
            },
            pickles::recorded::RecordedProgramBranch {
                circuit: tiny_circuit(),
                witness: vec![Fp::from(6u64), Fp::from(36u64)],
                proofs_verified: 1,
            },
            pickles::recorded::RecordedProgramBranch {
                circuit: tiny_circuit(),
                witness: vec![Fp::from(6u64), Fp::from(36u64)],
                proofs_verified: 2,
            },
        ];
        let compiled =
            pickles::recorded::RecordedCompiledProgram::compile(branches).expect("compile");
        for (i, label) in compiled.wrap_gate_labels_for_tests(5225, 5245) {
            eprintln!("row {i}: {label}");
        }
        return;
    }
    let witness = vec![Fp::from(6u64), Fp::from(36u64)];

    if mode == "method" {
        let hook: fn(snarky::api::CompileProfile) = |p| {
            eprintln!(
                "  [index] lowering={}ms cs={}ms lagrange={}ms index={}ms",
                p.lowering_micros / 1000,
                p.constraint_system_micros / 1000,
                p.lagrange_micros / 1000,
                p.prover_index_micros / 1000
            );
        };
        snarky::api::set_compile_profile_hook(Some(hook));
        // Warm the process-global SRS first to isolate their cost.
        let ts = Instant::now();
        let tick = pickles::common::tick_srs(1 << 16);
        eprintln!("tick SRS create: {:.2}s", ts.elapsed().as_secs_f64());
        let ts2 = Instant::now();
        let tock = pickles::common::tock_srs(1 << 15);
        eprintln!("tock SRS create: {:.2}s", ts2.elapsed().as_secs_f64());
        use poly_commitment::SRS as _;
        for log2 in [9u32, 13, 14, 15] {
            let t = Instant::now();
            if log2 <= 15 {
                let d = ark_poly::EvaluationDomain::<mina_curves::pasta::Fp>::new(1usize << log2)
                    .unwrap();
                let _ = tick.get_lagrange_basis(d);
                eprintln!("tick lagrange 2^{log2}: {:.2}s", t.elapsed().as_secs_f64());
            }
        }
        for log2 in [13u32, 15] {
            let t = Instant::now();
            let d =
                ark_poly::EvaluationDomain::<mina_curves::pasta::Fq>::new(1usize << log2).unwrap();
            let _ = tock.get_lagrange_basis(d);
            eprintln!("tock lagrange 2^{log2}: {:.2}s", t.elapsed().as_secs_f64());
        }
        // Mimic mina-runtime compile_circuit for pv=2 (the slowest branch).
        let t0 = Instant::now();
        let base =
            pickles::recorded::RecordedCompiledBase::compile(tiny_circuit(), witness.clone())
                .expect("base");
        eprintln!("base compile: {:.2}s", t0.elapsed().as_secs_f64());
        let t1 = Instant::now();
        let donor = base.donor_handle(&witness).expect("donor");
        eprintln!("donor: {:.2}s", t1.elapsed().as_secs_f64());
        let t2 = Instant::now();
        let _n2 = pickles::recorded::RecordedCompiledN2::compile(
            &donor,
            &donor,
            tiny_circuit(),
            witness.clone(),
        )
        .expect("n2");
        eprintln!("N2 compile: {:.2}s", t2.elapsed().as_secs_f64());
        let t3 = Instant::now();
        let _n1 = pickles::recorded::RecordedCompiledN1::compile(&donor, tiny_circuit(), witness)
            .expect("n1");
        eprintln!("N1 compile: {:.2}s", t3.elapsed().as_secs_f64());
        eprintln!("TOTAL: {:.2}s", t0.elapsed().as_secs_f64());
        return;
    }

    if mode == "base" {
        let t0 = Instant::now();
        let _c = pickles::recorded::RecordedCompiledBase::compile(tiny_circuit(), witness)
            .expect("compile");
        eprintln!("TOTAL base compile: {:.1}s", t0.elapsed().as_secs_f64());
        return;
    }

    // Mirror the AddZkProgram bench: one N0 branch, one N1, one N2.
    let branches = vec![
        pickles::recorded::RecordedProgramBranch {
            circuit: tiny_circuit(),
            witness: witness.clone(),
            proofs_verified: 0,
        },
        pickles::recorded::RecordedProgramBranch {
            circuit: tiny_circuit(),
            witness: witness.clone(),
            proofs_verified: 1,
        },
        pickles::recorded::RecordedProgramBranch {
            circuit: tiny_circuit(),
            witness,
            proofs_verified: 2,
        },
    ];
    let t0 = Instant::now();
    let _compiled = pickles::recorded::RecordedCompiledProgram::compile(branches).expect("compile");
    eprintln!("TOTAL program compile: {:.1}s", t0.elapsed().as_secs_f64());
}
