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
    let witness = vec![Fp::from(6u64), Fp::from(36u64)];

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
    let _compiled =
        pickles::recorded::RecordedCompiledProgram::compile(branches).expect("compile");
    eprintln!("TOTAL program compile: {:.1}s", t0.elapsed().as_secs_f64());
}
