//! End-to-end test of the recorded-circuit pipeline: a circuit encoded as
//! the host-language JSON envelope is proved through the base-case Pickles
//! backend and its proof verified standalone against the side-loaded key.

use mina_curves::pasta::Fp;
use pickles::recorded::{
    prove_recorded_base_case, LinComb, RecordedCircuit, RecordedCircuitError, RecordedConstraint,
    RecordedProveError,
};
use pickles::verify::{verify_side_loaded_base_case, StandaloneVerifyError};

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
