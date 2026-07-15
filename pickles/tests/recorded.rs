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
        aux_count: 2,
        output: vec![LinComb::var(1)],
        constraints: vec![RecordedConstraint::Square {
            v: LinComb::var(0),
            square: LinComb::var(1),
        }],
    }
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
    let proved = program
        .prove_n0(0, vec![Fp::from(6u64), Fp::from(36u64)])
        .unwrap();
    assert_eq!(proved.app_state, vec![Fp::from(36u64)]);
    let (accumulators, challenges, vk) = proved.program_verification_messages().unwrap();
    pickles::verify::verify_side_loaded_with_step_vk(
        &proved.app_state,
        Some(&vk),
        &accumulators,
        &challenges,
        &proved.proof,
    )
    .unwrap();
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
