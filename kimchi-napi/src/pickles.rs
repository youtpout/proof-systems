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
