//! End-to-end test of the recorded-circuit pipeline: a circuit encoded as
//! the host-language JSON envelope is proved through the base-case Pickles
//! backend and its proof verified standalone against the side-loaded key.

use mina_curves::pasta::Fp;
use pickles::{
    recorded::{
        prove_recorded_base_case, LinComb, RecordedCircuit, RecordedCircuitError,
        RecordedConstraint, RecordedProveError,
    },
    verify::{verify_side_loaded_base_case, StandaloneVerifyError},
};

/// x0 = witness, x1 = x0², output = x1.
fn square_circuit() -> RecordedCircuit {
    RecordedCircuit {
        previous_state_slots: vec![],
        previous_proof_widths: vec![],
        aux_count: 2,
        output: vec![LinComb::var(1)],
        constraints: vec![RecordedConstraint::Square {
            v: LinComb::var(0),
            square: LinComb::var(1),
        }],
    }
}

/// Two-field app state: 56 VK coordinates + 2 fields fill the Poseidon rate
/// exactly (the o1js Add program shape) — regression for the full-pending-
/// rate messages digest through a real recursive cycle.
#[test]
fn recorded_program_two_field_state_proves_n0_then_n1() {
    use pickles::recorded::{RecordedCompiledProgram, RecordedProgramBranch};

    let circuit = RecordedCircuit {
        previous_state_slots: vec![],
        previous_proof_widths: vec![],
        aux_count: 2,
        output: vec![LinComb::var(0), LinComb::var(1)],
        constraints: vec![RecordedConstraint::Square {
            v: LinComb::var(0),
            square: LinComb::var(1),
        }],
    };
    let branches = (0..=1)
        .map(|proofs_verified| RecordedProgramBranch {
            circuit: circuit.clone(),
            witness: vec![Fp::from(6u64), Fp::from(36u64)],
            proofs_verified,
        })
        .collect();
    let mut program = RecordedCompiledProgram::compile(branches).unwrap();
    let n0 = program
        .prove_n0(0, vec![Fp::from(6u64), Fp::from(36u64)])
        .unwrap();
    assert_eq!(n0.app_state, vec![Fp::from(6u64), Fp::from(36u64)]);
    {
        let (accumulators, challenges, vk) = n0.program_verification_messages().unwrap();
        pickles::verify::verify_side_loaded_with_step_vk(
            &n0.app_state,
            Some(&vk),
            &accumulators,
            &challenges,
            &n0.proof,
        )
        .expect("host verification of the two-field N0 proof");
    }
    let n1 = program
        .prove_n1(1, &n0, vec![Fp::from(6u64), Fp::from(36u64)])
        .unwrap();
    assert_eq!(n1.app_state, vec![Fp::from(6u64), Fp::from(36u64)]);
}

#[test]
fn recorded_circuit_json_round_trips() {
    let circuit = square_circuit();
    let json = serde_json::to_string(&circuit).unwrap();
    assert_eq!(
        serde_json::from_str::<RecordedCircuit>(&json).unwrap(),
        circuit
    );
    // Decimal-string field encoding, o1js-friendly.
    assert!(json.contains("\"terms\":[[\"1\",0]]"));
}

#[test]
fn recorded_circuit_validation_rejects_bad_shapes() {
    let mut circuit = square_circuit();
    circuit.output = vec![LinComb::var(7)];
    assert_eq!(
        circuit.validate(),
        Err(RecordedCircuitError::VariableOutOfRange(7))
    );

    assert!(matches!(
        prove_recorded_base_case(square_circuit(), vec![Fp::from(3u64)]),
        Err(RecordedProveError::Circuit(
            RecordedCircuitError::WrongWitnessLength(1)
        ))
    ));
}

#[test]
fn recorded_square_circuit_proves_and_verifies_standalone() {
    let witness = vec![Fp::from(6u64), Fp::from(36u64)];
    let proved = prove_recorded_base_case(square_circuit(), witness).unwrap();
    assert_eq!(proved.app_state, vec![Fp::from(36u64)]);

    // The proof verifies standalone against its embedded side-loaded key.
    verify_side_loaded_base_case(&proved.app_state, &proved.proof).unwrap();
    assert!(matches!(
        verify_side_loaded_base_case(&[Fp::from(35u64)], &proved.proof),
        Err(StandaloneVerifyError::AppStateMismatch)
    ));

    // An inconsistent witness (6² ≠ 35) is refused at proving time by the
    // constraint checker (currently a panic inside `prove_base_case`, whose
    // step-prove unwraps — hardening tracked separately).
    assert!(std::panic::catch_unwind(|| prove_recorded_base_case(
        square_circuit(),
        vec![Fp::from(6u64), Fp::from(35u64)]
    ))
    .is_err());
}

#[test]
fn recorded_compiled_base_reuses_indexes_across_witnesses() {
    let mut compiled = pickles::recorded::RecordedCompiledBase::compile(
        square_circuit(),
        vec![Fp::from(6u64), Fp::from(36u64)],
    )
    .unwrap();
    for (x, square) in [(6u64, 36u64), (7u64, 49u64)] {
        let proved = compiled
            .prove_keep(vec![Fp::from(x), Fp::from(square)])
            .unwrap();
        assert_eq!(proved.app_state, vec![Fp::from(square)]);
        verify_side_loaded_base_case(&proved.app_state, &proved.proof).unwrap();
    }
}

#[test]
fn recorded_compilation_does_not_require_a_satisfying_witness() {
    // ZkProgram.compile() analyzes arbitrary methods with placeholder values.
    // Compilation must therefore depend on the constraint shape, not on those
    // values satisfying the application circuit.
    let mut compiled = pickles::recorded::RecordedCompiledBase::compile(
        square_circuit(),
        vec![Fp::from(6u64), Fp::from(35u64)],
    )
    .unwrap();
    let proved = compiled
        .prove_keep(vec![Fp::from(6u64), Fp::from(36u64)])
        .unwrap();
    verify_side_loaded_base_case(&proved.app_state, &proved.proof).unwrap();
}

#[test]
fn recorded_program_compiles_n0_n1_n2_with_one_wrap_key() {
    use pickles::recorded::{RecordedCompiledProgram, RecordedProgramBranch};

    let branches = (0..=2)
        .map(|proofs_verified| RecordedProgramBranch {
            circuit: square_circuit(),
            witness: vec![Fp::from(6u64), Fp::from(36u64)],
            proofs_verified,
        })
        .collect();
    let mut program = RecordedCompiledProgram::compile(branches).unwrap();
    assert_eq!(program.branch_count(), 3);
    assert_eq!(program.wrap_verification_key_points().len(), 28);
    let n0 = program
        .prove_n0(0, vec![Fp::from(6u64), Fp::from(36u64)])
        .unwrap();
    let verify = |proved: &pickles::recorded::RecordedProofHandle| {
        let (accumulators, challenges, vk) = proved.program_verification_messages().unwrap();
        pickles::verify::verify_side_loaded_with_step_vk(
            &proved.app_state,
            Some(&vk),
            &accumulators,
            &challenges,
            &proved.proof,
        )
        .unwrap();
    };
    assert_eq!(n0.app_state, vec![Fp::from(36u64)]);
    verify(&n0);

    let n1 = program
        .prove_n1(1, &n0, vec![Fp::from(7u64), Fp::from(49u64)])
        .unwrap();
    assert_eq!(n1.app_state, vec![Fp::from(49u64)]);
    verify(&n1);

    let n2 = program
        .prove_n2(2, [&n0, &n1], vec![Fp::from(8u64), Fp::from(64u64)])
        .unwrap();
    assert_eq!(n2.app_state, vec![Fp::from(64u64)]);
    verify(&n2);
}

#[test]
#[ignore = "diagnostic dump, run explicitly"]
fn dump_labeled_wrap_for_b_actual_probe() {
    use pickles::recorded::{
        dump_recorded_program_circuits, RecordedCircuit, RecordedProgramBranch,
    };

    #[derive(serde::Deserialize)]
    struct BranchJson {
        #[serde(rename = "proofsVerified")]
        proofs_verified: u8,
        circuit: RecordedCircuit,
    }
    // Recorded add-program branches (init pv0 / update pv1 / merge pv2) as
    // dumped by o1js's `rust-pickles-program-gates-diff` harness. Point
    // WRAP_BRANCHES_JSON at that dump; skip if it is not present.
    let path = std::env::var("WRAP_BRANCHES_JSON")
        .unwrap_or_else(|_| "/tmp/claude-1000/program-branches.json".to_string());
    let Ok(raw) = std::fs::read_to_string(&path) else {
        eprintln!("skipping: {path} not found (set WRAP_BRANCHES_JSON)");
        return;
    };
    let parsed: Vec<BranchJson> = serde_json::from_str(&raw).unwrap();
    let branches = parsed
        .into_iter()
        .map(|b| RecordedProgramBranch {
            witness: vec![Fp::from(0u64); b.circuit.aux_count as usize],
            circuit: b.circuit,
            proofs_verified: b.proofs_verified,
        })
        .collect();
    let json = dump_recorded_program_circuits(branches).unwrap();
    std::fs::write("/tmp/claude-1000/wrap-labeled-rust.json", json).unwrap();
    eprintln!("wrote /tmp/claude-1000/wrap-labeled-rust.json (add-program branches)");
}

#[test]
#[ignore = "diagnostic VK decode+diff, run explicitly"]
fn decode_and_diff_add_vk_against_jsoo() {
    use pickles::mina_bin_prot::SideLoadedVerificationKeyV2;
    use pickles::recorded::{RecordedCircuit, RecordedCompiledProgram, RecordedProgramBranch};

    // jsoo side-loaded VK, raw bin_prot bytes (base64-decoded o1js
    // VerificationKey.data): [2,1] header, 7 sigma + 15 coefficient + 6
    // selector commitments, each an uncompressed Pallas point.
    let vk_bytes = match std::fs::read("/tmp/claude-1000/add-vk-jsoo.bin") {
        Ok(b) => b,
        Err(_) => {
            eprintln!("skipping: /tmp/claude-1000/add-vk-jsoo.bin not found");
            return;
        }
    };
    let jsoo = SideLoadedVerificationKeyV2::from_bin_prot(&vk_bytes).unwrap();

    #[derive(serde::Deserialize)]
    struct BranchJson {
        #[serde(rename = "proofsVerified")]
        proofs_verified: u8,
        circuit: RecordedCircuit,
    }
    let raw = match std::fs::read_to_string("/tmp/claude-1000/program-branches.json") {
        Ok(r) => r,
        Err(_) => {
            eprintln!("skipping: program-branches.json not found");
            return;
        }
    };
    let parsed: Vec<BranchJson> = serde_json::from_str(&raw).unwrap();
    let branches = parsed
        .into_iter()
        .map(|b| RecordedProgramBranch {
            witness: vec![Fp::from(0u64); b.circuit.aux_count as usize],
            circuit: b.circuit,
            proofs_verified: b.proofs_verified,
        })
        .collect();
    let program = RecordedCompiledProgram::compile(branches).unwrap();
    let rust = program.wrap_verification_key_points();

    assert_eq!(jsoo.commitments.len(), 28);
    assert_eq!(rust.len(), 28);
    let label = |i: usize| -> String {
        if i < 7 {
            format!("sigma[{i}]")
        } else if i < 22 {
            format!("coefficient[{}]", i - 7)
        } else {
            ["generic", "psm", "complete_add", "mul", "emul", "endomul_scalar"][i - 22].to_string()
        }
    };
    let mut equal = 0;
    for i in 0..28 {
        let same = jsoo.commitments[i] == rust[i];
        if same {
            equal += 1;
        }
        eprintln!(
            "  [{i:2}] {:<16} {}",
            label(i),
            if same { "MATCH" } else { "DIFFERS" }
        );
    }
    eprintln!("=== equal commitments: {equal}/28 ===");
}

#[test]
fn recorded_compiled_base_cache_round_trips_and_rejects_corruption() {
    use pickles::recorded::RecordedCompiledBase;

    let circuit = square_circuit();
    let compiled =
        RecordedCompiledBase::compile(circuit.clone(), vec![Fp::from(3u64), Fp::from(9u64)])
            .unwrap();
    let bytes = compiled.to_cache_bytes().unwrap();
    let mut restored = RecordedCompiledBase::from_cache_bytes(
        circuit.clone(),
        vec![Fp::from(4u64), Fp::from(16u64)],
        &bytes,
    )
    .unwrap();
    let proof = restored
        .prove_keep(vec![Fp::from(4u64), Fp::from(16u64)])
        .unwrap();
    assert_eq!(proof.app_state, vec![Fp::from(16u64)]);

    let mut corrupted = bytes;
    let middle = corrupted.len() / 2;
    corrupted[middle] ^= 1;
    assert!(RecordedCompiledBase::from_cache_bytes(
        circuit,
        vec![Fp::from(5u64), Fp::from(25u64)],
        &corrupted,
    )
    .is_err());
}

/// Recorded EC complete addition of two Vesta points (base field Fp),
/// output = x3. Witness layout: [x1, y1, x2, y2, x3, y3, slope, x21_inv].
fn ec_add_circuit() -> RecordedCircuit {
    use pickles::recorded::RecordedConstraint::EcAddComplete;
    let zero = LinComb::default;
    RecordedCircuit {
        previous_state_slots: vec![],
        previous_proof_widths: vec![],
        aux_count: 8,
        output: vec![LinComb::var(4)],
        constraints: vec![EcAddComplete {
            p1: (LinComb::var(0), LinComb::var(1)),
            p2: (LinComb::var(2), LinComb::var(3)),
            p3: (LinComb::var(4), LinComb::var(5)),
            inf: zero(),
            same_x: zero(),
            slope: LinComb::var(6),
            inf_z: zero(),
            x21_inv: LinComb::var(7),
        }],
    }
}

#[test]
fn recorded_gate_variants_round_trip_and_validate() {
    use pickles::recorded::RecordedConstraint;

    let range_check0 = RecordedCircuit {
        previous_state_slots: vec![],
        previous_proof_widths: vec![],
        aux_count: 15,
        output: vec![],
        constraints: vec![RecordedConstraint::RangeCheck0 {
            row: (0..15).map(LinComb::var).collect(),
            compact: Fp::from(0u64),
        }],
    };
    let json = serde_json::to_string(&range_check0).unwrap();
    assert_eq!(
        serde_json::from_str::<RecordedCircuit>(&json).unwrap(),
        range_check0
    );

    // Wrong row width is rejected.
    let bad = RecordedCircuit {
        previous_state_slots: vec![],
        previous_proof_widths: vec![],
        aux_count: 15,
        output: vec![],
        constraints: vec![RecordedConstraint::Lookup {
            row: (0..5).map(LinComb::var).collect(),
        }],
    };
    assert_eq!(
        bad.validate(),
        Err(pickles::recorded::RecordedCircuitError::MalformedRow {
            expected: 7,
            actual: 5
        })
    );

    let ec = ec_add_circuit();
    let json = serde_json::to_string(&ec).unwrap();
    assert_eq!(serde_json::from_str::<RecordedCircuit>(&json).unwrap(), ec);
}

#[test]
fn recorded_ec_add_circuit_proves_and_verifies_standalone() {
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::Field;
    use mina_curves::pasta::Pallas;

    // Two distinct Pallas points (coordinates in Fp, the step circuit field)
    // and their sum, plus the CompleteAdd witnesses (distinct x, so
    // inf = same_x = inf_z = 0).
    let p1 = Pallas::generator();
    let p2 = (p1 + p1).into_affine();
    let p3 = (p1 + p2).into_affine();
    let x21_inv = (p2.x - p1.x).inverse().unwrap();
    let slope = (p2.y - p1.y) * x21_inv;
    let witness = vec![p1.x, p1.y, p2.x, p2.y, p3.x, p3.y, slope, x21_inv];

    let proved = prove_recorded_base_case(ec_add_circuit(), witness).unwrap();
    assert_eq!(proved.app_state, vec![p3.x]);
    verify_side_loaded_base_case(&proved.app_state, &proved.proof).unwrap();
}

#[test]
fn recorded_n1_cycle_proves_and_verifies_standalone() {
    use pickles::{recorded::prove_recorded_n1, verify::verify_side_loaded_with_step_vk};

    let witness = vec![Fp::from(8u64), Fp::from(64u64)];
    let proved = prove_recorded_n1(square_circuit(), witness).unwrap();
    assert_eq!(proved.app_state, vec![Fp::from(64u64)]);

    // Standalone verification: the digest binds the base program's wrap VK
    // (dlog_plonk_index) together with the recursion messages.
    let vk = verify_side_loaded_with_step_vk(
        &proved.app_state,
        Some(proved.dlog_plonk_index.as_slice()),
        &[proved.challenge_polynomial_commitment],
        &[proved.old_bulletproof_challenges.clone()],
        &proved.proof,
    )
    .unwrap();
    assert_eq!(
        vk.proofs_verified,
        pickles::composition_types::ProofsVerified::N1
    );

    // Without the recursion messages the digest binding fails.
    assert!(verify_side_loaded_with_step_vk(
        &proved.app_state,
        Some(proved.dlog_plonk_index.as_slice()),
        &[],
        &[],
        &proved.proof,
    )
    .is_err());
}

#[test]
fn recorded_compiled_n1_reuses_step_and_wrap_indexes() {
    use pickles::{
        recorded::{prove_recorded_base_case_keep, RecordedCompiledN1},
        verify::verify_side_loaded_with_step_vk,
    };

    let base =
        prove_recorded_base_case_keep(square_circuit(), vec![Fp::from(6u64), Fp::from(36u64)])
            .unwrap();
    let witness = vec![Fp::from(7u64), Fp::from(49u64)];
    let mut compiled =
        RecordedCompiledN1::compile(&base, square_circuit(), witness.clone()).unwrap();
    for witness in [
        vec![Fp::from(7u64), Fp::from(49u64)],
        vec![Fp::from(8u64), Fp::from(64u64)],
    ] {
        let proved = compiled.prove_keep(&base, witness).unwrap();
        let recursive = proved.to_recorded_n1_proof().unwrap();
        verify_side_loaded_with_step_vk(
            &recursive.app_state,
            Some(&recursive.dlog_plonk_index),
            &[recursive.challenge_polynomial_commitment],
            &[recursive.old_bulletproof_challenges],
            &recursive.proof,
        )
        .unwrap();
    }

    // The stable recursive shape is compiled eagerly alongside the first
    // base-to-recursive transition and can be reused without falling back to
    // a compile-on-prove path.
    let first = compiled
        .prove_keep(&base, vec![Fp::from(9u64), Fp::from(81u64)])
        .unwrap();
    let second = compiled
        .prove_keep(&first, vec![Fp::from(10u64), Fp::from(100u64)])
        .unwrap();
    assert_eq!(second.app_state, vec![Fp::from(100u64)]);
}

#[test]
fn recorded_stable_n1_chain_proves_and_verifies_standalone() {
    use pickles::{recorded::prove_recorded_stable_n1, verify::verify_side_loaded_with_step_vk};

    let witness = vec![Fp::from(9u64), Fp::from(81u64)];
    let proved = prove_recorded_stable_n1(square_circuit(), witness, 1).unwrap();
    assert_eq!(proved.app_state, vec![Fp::from(81u64)]);
    assert_eq!(proved.stable_cycles, 2);

    let vk = verify_side_loaded_with_step_vk(
        &proved.app_state,
        Some(proved.dlog_plonk_index.as_slice()),
        &[proved.challenge_polynomial_commitment],
        &[proved.old_bulletproof_challenges.clone()],
        &proved.proof,
    )
    .unwrap();
    assert_eq!(
        vk.proofs_verified,
        pickles::composition_types::ProofsVerified::N1
    );

    assert!(matches!(
        verify_side_loaded_with_step_vk(
            &[Fp::from(82u64)],
            Some(proved.dlog_plonk_index.as_slice()),
            &[proved.challenge_polynomial_commitment],
            &[proved.old_bulletproof_challenges.clone()],
            &proved.proof,
        ),
        Err(StandaloneVerifyError::AppStateMismatch)
    ));
}

#[test]
fn recorded_n2_cycle_proves_and_verifies_standalone() {
    std::thread::Builder::new()
        .name("recorded-n2-proof".to_string())
        .stack_size(128 * 1024 * 1024)
        .spawn(|| {
            use pickles::{recorded::prove_recorded_n2, verify::verify_side_loaded_with_step_vk};

            let first = vec![Fp::from(10u64), Fp::from(100u64)];
            let second = vec![Fp::from(11u64), Fp::from(121u64)];
            let app_state = vec![Fp::from(221u64)];
            let proved =
                prove_recorded_n2(square_circuit(), first, second, app_state.clone()).unwrap();
            assert_eq!(proved.app_state, app_state);

            let vk = verify_side_loaded_with_step_vk(
                &proved.app_state,
                Some(proved.dlog_plonk_index.as_slice()),
                &proved.challenge_polynomial_commitments,
                &proved.old_bulletproof_challenges,
                &proved.proof,
            )
            .unwrap();
            assert_eq!(
                vk.proofs_verified,
                pickles::composition_types::ProofsVerified::N2
            );

            assert!(matches!(
                verify_side_loaded_with_step_vk(
                    &[Fp::from(222u64)],
                    Some(proved.dlog_plonk_index.as_slice()),
                    &proved.challenge_polynomial_commitments,
                    &proved.old_bulletproof_challenges,
                    &proved.proof,
                ),
                Err(StandaloneVerifyError::AppStateMismatch)
            ));
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn recorded_n2_over_two_kept_bases_executes_the_new_application() {
    std::thread::Builder::new()
        .name("recorded-n2-over-kept-bases".to_string())
        .stack_size(128 * 1024 * 1024)
        .spawn(|| {
            use pickles::{
                recorded::{prove_recorded_base_case_keep, prove_recorded_n2_over_base_handles},
                verify::verify_side_loaded_with_step_vk,
            };

            let first = prove_recorded_base_case_keep(
                square_circuit(),
                vec![Fp::from(3u64), Fp::from(9u64)],
            )
            .unwrap();
            let second = prove_recorded_base_case_keep(
                square_circuit(),
                vec![Fp::from(4u64), Fp::from(16u64)],
            )
            .unwrap();
            let app = RecordedCircuit {
        previous_state_slots: vec![],
        previous_proof_widths: vec![],
                aux_count: 3,
                output: vec![LinComb::var(2)],
                constraints: vec![RecordedConstraint::R1cs {
                    a: LinComb::var(0),
                    b: LinComb::var(1),
                    c: LinComb::var(2),
                }],
            };
            let proved = prove_recorded_n2_over_base_handles(
                &first,
                &second,
                app,
                vec![Fp::from(6u64), Fp::from(7u64), Fp::from(42u64)],
            )
            .unwrap();
            assert_eq!(proved.app_state, [Fp::from(42u64)]);
            let vk = verify_side_loaded_with_step_vk(
                &proved.app_state,
                Some(proved.dlog_plonk_index.as_slice()),
                &proved.challenge_polynomial_commitments,
                &proved.old_bulletproof_challenges,
                &proved.proof,
            )
            .unwrap();
            assert_eq!(
                vk.proofs_verified,
                pickles::composition_types::ProofsVerified::N2
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn recorded_compiled_n2_reuses_step_and_wrap_indexes() {
    use pickles::recorded::{RecordedCompiledBase, RecordedCompiledN2};

    let mut base =
        RecordedCompiledBase::compile(square_circuit(), vec![Fp::from(3u64), Fp::from(9u64)])
            .unwrap();
    let first = base
        .prove_keep(vec![Fp::from(4u64), Fp::from(16u64)])
        .unwrap();
    let second = base
        .prove_keep(vec![Fp::from(5u64), Fp::from(25u64)])
        .unwrap();
    let mut compiled = RecordedCompiledN2::compile(
        &first,
        &second,
        square_circuit(),
        vec![Fp::from(6u64), Fp::from(36u64)],
    )
    .unwrap();
    let proof = compiled
        .prove(&first, &second, vec![Fp::from(7u64), Fp::from(49u64)])
        .unwrap();
    assert_eq!(proof.app_state, vec![Fp::from(49u64)]);
    pickles::verify::verify_side_loaded_with_step_vk(
        &proof.app_state,
        Some(&proof.dlog_plonk_index),
        &proof.challenge_polynomial_commitments,
        &proof.old_bulletproof_challenges,
        &proof.proof,
    )
    .unwrap();
}

#[test]
fn recorded_chained_n1_runs_new_circuit_over_kept_base() {
    use pickles::{
        recorded::{prove_recorded_base_case_keep, prove_recorded_n1_over_keep},
        verify::verify_side_loaded_with_step_vk,
    };

    // Base proof: the square circuit, kept alive for chaining.
    let handle =
        prove_recorded_base_case_keep(square_circuit(), vec![Fp::from(5u64), Fp::from(25u64)])
            .unwrap();
    assert_eq!(handle.app_state, vec![Fp::from(25u64)]);
    verify_side_loaded_base_case(&handle.app_state, &handle.proof).unwrap();

    // Recursive step: a *different* circuit (x·y = z) runs in-step while
    // verifying the kept base proof — the ZkProgram SelfProof shape.
    let mul_circuit = RecordedCircuit {
        previous_state_slots: vec![],
        previous_proof_widths: vec![],
        aux_count: 3,
        output: vec![LinComb::var(2)],
        constraints: vec![RecordedConstraint::R1cs {
            a: LinComb::var(0),
            b: LinComb::var(1),
            c: LinComb::var(2),
        }],
    };
    let witness = vec![Fp::from(6u64), Fp::from(7u64), Fp::from(42u64)];
    let first_handle = prove_recorded_n1_over_keep(&handle, mul_circuit, witness).unwrap();
    let proved = first_handle.to_recorded_n1_proof().unwrap();
    assert_eq!(proved.app_state, vec![Fp::from(42u64)]);

    // The digest binds the *new* circuit's app state together with the
    // verified base proof's accumulator and the base program's wrap VK.
    let vk = verify_side_loaded_with_step_vk(
        &proved.app_state,
        Some(proved.dlog_plonk_index.as_slice()),
        &[proved.challenge_polynomial_commitment],
        &[proved.old_bulletproof_challenges.clone()],
        &proved.proof,
    )
    .unwrap();
    assert_eq!(
        vk.proofs_verified,
        pickles::composition_types::ProofsVerified::N1
    );

    // The base program's app state does not satisfy the new digest.
    assert!(matches!(
        verify_side_loaded_with_step_vk(
            &handle.app_state,
            Some(proved.dlog_plonk_index.as_slice()),
            &[proved.challenge_polynomial_commitment],
            &[proved.old_bulletproof_challenges.clone()],
            &proved.proof,
        ),
        Err(StandaloneVerifyError::AppStateMismatch)
    ));

    // The recursive handle can itself be consumed by another call without
    // replaying either previous witness.
    let second_handle = prove_recorded_n1_over_keep(
        &first_handle,
        square_circuit(),
        vec![Fp::from(8u64), Fp::from(64u64)],
    )
    .unwrap();
    let second = second_handle.to_recorded_n1_proof().unwrap();
    assert_eq!(second.app_state, vec![Fp::from(64u64)]);
    let vk = verify_side_loaded_with_step_vk(
        &second.app_state,
        Some(second.dlog_plonk_index.as_slice()),
        &[second.challenge_polynomial_commitment],
        &[second.old_bulletproof_challenges],
        &second.proof,
    )
    .unwrap();
    assert_eq!(
        vk.proofs_verified,
        pickles::composition_types::ProofsVerified::N1
    );
}

/// The single-pass program compile must reproduce exactly the artifacts the
/// historical multi-pass fixpoint iteration converged to: identical
/// per-branch step verification keys and an identical shared wrap key.
#[test]
fn program_single_pass_matches_multipass_reference() {
    use pickles::recorded::{RecordedCompiledProgram, RecordedProgramBranch};
    let branches: Vec<RecordedProgramBranch> = [0u8, 1, 2]
        .into_iter()
        .map(|proofs_verified| RecordedProgramBranch {
            circuit: square_circuit(),
            witness: vec![Fp::from(6u64), Fp::from(36u64)],
            proofs_verified,
        })
        .collect();
    let single = RecordedCompiledProgram::compile(branches.clone()).expect("single-pass compile");
    let reference = RecordedCompiledProgram::compile_multipass_reference(branches)
        .expect("multi-pass reference compile");
    assert_eq!(
        single.wrap_branches_for_tests(),
        reference.wrap_branches_for_tests(),
        "per-branch step verification keys diverged from the multi-pass reference"
    );
    assert_eq!(
        single.wrap_verification_key_points(),
        reference.wrap_verification_key_points(),
        "shared wrap verification key diverged from the multi-pass reference"
    );
}

/// The proof-free N1 compile (dummy shape donors, OCaml-style) must produce
/// exactly the same compiled indexes as the historical variant that ran three
/// bootstrap proofs.
#[test]
fn n1_proof_free_compile_matches_bootstrap_reference() {
    use pickles::recorded::{RecordedCompiledBase, RecordedCompiledN1};
    let circuit = square_circuit();
    let witness = vec![Fp::from(6u64), Fp::from(36u64)];
    let mut base = RecordedCompiledBase::compile(circuit.clone(), witness.clone()).expect("base");
    let previous = base.prove_keep(witness.clone()).expect("base proof");
    let proof_free =
        RecordedCompiledN1::compile(&previous, circuit.clone(), witness.clone()).expect("N1");
    let reference = RecordedCompiledN1::compile_with_bootstrap_proofs_reference(
        &previous,
        circuit.clone(),
        witness.clone(),
    )
    .expect("N1 reference");
    assert_eq!(
        proof_free.index_fingerprint_for_tests(),
        reference.index_fingerprint_for_tests(),
        "N1 compiled indexes diverged from the bootstrap-proof reference"
    );
}

/// Same equivalence for the width-2 (N2) compile.
#[test]
fn n2_proof_free_compile_matches_bootstrap_reference() {
    use pickles::recorded::{RecordedCompiledBase, RecordedCompiledN2};
    let circuit = square_circuit();
    let witness = vec![Fp::from(6u64), Fp::from(36u64)];
    let mut base = RecordedCompiledBase::compile(circuit.clone(), witness.clone()).expect("base");
    let previous = base.prove_keep(witness.clone()).expect("base proof");
    let proof_free =
        RecordedCompiledN2::compile(&previous, &previous, circuit.clone(), witness.clone())
            .expect("N2");
    let reference = RecordedCompiledN2::compile_with_bootstrap_proofs_reference(
        &previous,
        &previous,
        circuit.clone(),
        witness.clone(),
    )
    .expect("N2 reference");
    assert_eq!(
        proof_free.index_fingerprint_for_tests(),
        reference.index_fingerprint_for_tests(),
        "N2 compiled indexes diverged from the bootstrap-proof reference"
    );
}

/// The compile-time template only donates proof-shaped VALUES: compiling N1
/// and N2 against the proof-free donor handle must produce exactly the same
/// indexes as compiling against a real base proof.
#[test]
fn donor_template_matches_real_template_for_recursive_compiles() {
    use pickles::recorded::{RecordedCompiledBase, RecordedCompiledN1, RecordedCompiledN2};
    let circuit = square_circuit();
    let witness = vec![Fp::from(6u64), Fp::from(36u64)];
    let mut base = RecordedCompiledBase::compile(circuit.clone(), witness.clone()).expect("base");
    let donor = base.donor_handle(&witness).expect("donor handle");
    let real = base.prove_keep(witness.clone()).expect("base proof");

    let n1_donor =
        RecordedCompiledN1::compile(&donor, circuit.clone(), witness.clone()).expect("N1 donor");
    let n1_real =
        RecordedCompiledN1::compile(&real, circuit.clone(), witness.clone()).expect("N1 real");
    assert_eq!(
        n1_donor.index_fingerprint_for_tests(),
        n1_real.index_fingerprint_for_tests(),
        "N1 indexes depend on template values"
    );

    let n2_donor = RecordedCompiledN2::compile(&donor, &donor, circuit.clone(), witness.clone())
        .expect("N2 donor");
    let n2_real =
        RecordedCompiledN2::compile(&real, &real, circuit.clone(), witness).expect("N2 real");
    assert_eq!(
        n2_donor.index_fingerprint_for_tests(),
        n2_real.index_fingerprint_for_tests(),
        "N2 indexes depend on template values"
    );
}

/// Cross-verification: a proof produced by STOCK o1js 2.15's jsoo prover
/// (whose VK is byte-identical to the branch's jsoo reference) must verify
/// through the rust side-loaded verifier. Reads the dumps produced by
/// /tmp/claude-1000/proofdump/dump-proof.mjs; skips when absent.
#[test]
#[ignore = "needs /tmp/claude-1000/proof-jsoo-update.json (stock o1js dump)"]
fn stock_jsoo_215_proof_cross_verifies() {
    use base64::prelude::*;
    use pickles::mina_bin_prot::WrapProofBaseV3;

    #[derive(serde::Deserialize)]
    struct JsonProof {
        #[serde(rename = "publicInput")]
        public_input: Vec<String>,
        #[serde(rename = "publicOutput")]
        public_output: Vec<String>,
        proof: String,
    }
    let vk_b64 = {
        let Ok(raw) = std::fs::read_to_string("/tmp/claude-1000/vk-jsoo-215.json") else {
            eprintln!("skipping: vk dump not found");
            return;
        };
        serde_json::from_str::<serde_json::Value>(&raw).unwrap()["data"]
            .as_str()
            .unwrap()
            .to_string()
    };
    let vk = pickles::mina_bin_prot::SideLoadedVerificationKeyV2::from_bin_prot(
        &BASE64_STANDARD.decode(&vk_b64).unwrap(),
    )
    .unwrap();
    let vk_base58 = pickles::side_loaded::SideLoadedVerificationKey::from_stable_v2(
        pickles::common::TICK_ROUNDS as u8,
        vk.clone(),
    )
    .unwrap()
    .to_stable_v2_base58()
    .unwrap();

    for name in ["init", "update"] {
        let path = format!("/tmp/claude-1000/proof-jsoo-{name}.json");
        let Ok(raw) = std::fs::read_to_string(&path) else {
            eprintln!("skipping {name}: {path} not found");
            continue;
        };
        let jp: JsonProof = serde_json::from_str(&raw).unwrap();
        let full = BASE64_STANDARD.decode(jp.proof.trim()).unwrap();
        // o1js `Proof.toJSON().proof` is base64 of the OCaml SEXP
        // representation (`((statement((proof …`), not Mina bin_prot.
        // Finishing this test needs the sexp -> flattened-statement +
        // wire-proof mapping (see /tmp/claude-1000/sexp2json.mjs for the
        // parsed structure); until then, report and skip.
        if full.starts_with(b"((") {
            eprintln!(
                "[{name}] o1js proof is SEXP-encoded ({} bytes) — decode mapping TODO, skipping",
                full.len()
            );
            continue;
        }
        let base = WrapProofBaseV3::from_mina_bin_prot(&full).unwrap();
        eprintln!(
            "[{name}] decoded: statement={} flattened={} step_cpcs={} step_chals={}x{} wrap_chals={}x{}",
            base.statement.len(),
            base.stable_statement.flattened.len(),
            base.stable_statement
                .messages_for_next_step_proof
                .challenge_polynomial_commitments
                .len(),
            base.stable_statement
                .messages_for_next_step_proof
                .old_bulletproof_challenges
                .len(),
            base.stable_statement
                .messages_for_next_step_proof
                .old_bulletproof_challenges
                .first()
                .map_or(0, Vec::len),
            base.stable_statement
                .messages_for_next_wrap_proof
                .old_bulletproof_challenges
                .len(),
            base.stable_statement
                .messages_for_next_wrap_proof
                .old_bulletproof_challenges
                .first()
                .map_or(0, Vec::len),
        );
        let app_state: Vec<Fp> = jp
            .public_input
            .iter()
            .chain(&jp.public_output)
            .map(|s| Fp::from(s.parse::<u64>().unwrap()))
            .collect();
        // The wrap proof's own accumulators: pickles pads them with the
        // canonical DUMMY wrap sg (constant), carrying only the Tock
        // challenge vectors in the stable statement's m4nwrap messages.
        let dummy_sg = pickles::dummy::pasta_dummy_wrap_sg();
        let proof = pickles::api::MinaWrapProof {
            statement: base.statement.clone(),
            wrap_wire_proof: base.proof.to_bin_prot().unwrap(),
            side_loaded_verification_key: vk_base58.clone(),
            wrap_recursion_commitments: vec![(dummy_sg.x, dummy_sg.y); 2],
            wrap_recursion_challenges: base
                .stable_statement
                .messages_for_next_wrap_proof
                .old_bulletproof_challenges
                .clone(),
        };
        let step_msgs = &base.stable_statement.messages_for_next_step_proof;
        let result = pickles::verify::verify_side_loaded(
            &app_state,
            &step_msgs.challenge_polynomial_commitments,
            &step_msgs.old_bulletproof_challenges,
            &proof,
        );
        match result {
            Ok(_) => eprintln!("[{name}] CROSS-VERIFIES with the rust verifier ✓"),
            Err(e) => eprintln!("[{name}] verify FAILED: {e:?}"),
        }
    }
}

/// Regenerates the embedded compile-time dummy blob
/// (`pickles/src/template_dummy.blob`). Run after any change to the template
/// base or bootstrap step circuits, then commit the new blob:
/// `cargo test -p pickles --release --test recorded generate_template_dummy_blob -- --ignored --nocapture`
#[test]
#[ignore]
fn generate_template_dummy_blob() {
    let bytes = pickles::recorded::template_dummy_blob_bytes();
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/src/template_dummy.blob");
    std::fs::write(path, &bytes).expect("write blob");
    eprintln!("wrote {} bytes to {path}", bytes.len());
}

/// The embedded dummy blob must exist and match the CURRENT template base
/// circuits (compile-only check, no proving). On failure, regenerate with
/// `generate_template_dummy_blob` above and commit the blob.
#[test]
fn template_dummy_blob_is_fresh() {
    let blob = pickles::recorded::template_blob_digests()
        .expect("embedded template dummy blob missing or undecodable — regenerate it");
    let live = pickles::recorded::template_live_digests();
    assert_eq!(
        blob, live,
        "template circuits drifted from the embedded dummy blob — regenerate it"
    );
}
