use mina_curves::pasta::Fp;
use napi::bindgen_prelude::*;
use napi_derive::napi;
use pickles::{
    api::{BaseCaseRuleBackend, StepApp},
    composition_types::ProofsVerified,
    inductive_rule::{InductiveRule, RuleId},
};
use snarky::{loc, FieldVar, RunState, SnarkyResult};

const SQUARE_STEP_ROUNDS: usize = 9;
const SQUARE_STATEMENT_LEN: usize = 13 + SQUARE_STEP_ROUNDS + 9;

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
