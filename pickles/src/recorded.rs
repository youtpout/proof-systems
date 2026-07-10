//! Recorded circuits: replayable constraint lists driven from a host
//! language (o1js over NAPI/WASM) and hosted by a Pickles step proof.
//!
//! A [`RecordedCircuit`] is the serialization-friendly form of an
//! application circuit: a number of witness variables, a list of kimchi
//! constraints over linear combinations of those variables, and the linear
//! combinations whose values form the application state. Replaying it inside
//! [`StepApp::main`] rebuilds the exact same gates at compile time and the
//! witness at prove time, so a circuit recorded by o1js's constraint-system
//! adapter can be proved by the base-case Pickles pipeline without any
//! host-language callback re-entering Rust.

use ark_ff::Zero;
use mina_curves::pasta::Fp;
use snarky::{
    constraint_system::{BasicInput, BasicSnarkyConstraint, KimchiConstraint, PoseidonInput},
    loc, FieldVar, RunState, SnarkyResult,
};

use crate::api::{MinaWrapProof, StepApp};

/// Serde for Pasta `Fp` as decimal strings — the o1js-friendly JSON form.
pub mod fp_decimal {
    use core::str::FromStr;
    use mina_curves::pasta::Fp;
    use serde::{Deserialize, Deserializer, Serializer};

    pub fn serialize<S: Serializer>(value: &Fp, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&value.to_string())
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<Fp, D::Error> {
        let repr = String::deserialize(deserializer)?;
        Fp::from_str(&repr).map_err(|_| serde::de::Error::custom("expected a decimal Pasta Fp"))
    }

    pub mod option {
        use super::*;

        pub fn serialize<S: Serializer>(
            value: &Option<Fp>,
            serializer: S,
        ) -> Result<S::Ok, S::Error> {
            match value {
                Some(value) => serializer.serialize_some(&value.to_string()),
                None => serializer.serialize_none(),
            }
        }

        pub fn deserialize<'de, D: Deserializer<'de>>(
            deserializer: D,
        ) -> Result<Option<Fp>, D::Error> {
            let repr = Option::<String>::deserialize(deserializer)?;
            repr.map(|repr| {
                Fp::from_str(&repr)
                    .map_err(|_| serde::de::Error::custom("expected a decimal Pasta Fp"))
            })
            .transpose()
        }
    }

    pub mod terms {
        use super::*;
        use serde::ser::SerializeSeq;

        pub fn serialize<S: Serializer>(
            value: &[(Fp, u32)],
            serializer: S,
        ) -> Result<S::Ok, S::Error> {
            let mut seq = serializer.serialize_seq(Some(value.len()))?;
            for (coeff, index) in value {
                seq.serialize_element(&(coeff.to_string(), index))?;
            }
            seq.end()
        }

        pub fn deserialize<'de, D: Deserializer<'de>>(
            deserializer: D,
        ) -> Result<Vec<(Fp, u32)>, D::Error> {
            let raw = Vec::<(String, u32)>::deserialize(deserializer)?;
            raw.into_iter()
                .map(|(coeff, index)| {
                    Fp::from_str(&coeff)
                        .map(|coeff| (coeff, index))
                        .map_err(|_| serde::de::Error::custom("expected a decimal Pasta Fp"))
                })
                .collect()
        }
    }
}

/// A linear combination `constant + Σ coeff·var` over the circuit's witness
/// variables (indexed in allocation order).
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct LinComb {
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        with = "fp_decimal::option"
    )]
    pub constant: Option<Fp>,
    #[serde(default, skip_serializing_if = "Vec::is_empty", with = "fp_decimal::terms")]
    pub terms: Vec<(Fp, u32)>,
}

impl LinComb {
    pub fn var(index: u32) -> Self {
        Self {
            constant: None,
            terms: vec![(Fp::from(1u64), index)],
        }
    }

    fn max_var(&self) -> Option<u32> {
        self.terms.iter().map(|&(_, index)| index).max()
    }

    fn resolve(&self, vars: &[FieldVar<Fp>]) -> FieldVar<Fp> {
        let mut acc = FieldVar::constant(self.constant.unwrap_or_else(Fp::zero));
        for &(coeff, index) in &self.terms {
            acc = &acc + &vars[index as usize].scale(coeff);
        }
        acc
    }

    fn evaluate(&self, values: &[Fp]) -> Fp {
        let mut acc = self.constant.unwrap_or_else(Fp::zero);
        for &(coeff, index) in &self.terms {
            acc += coeff * values[index as usize];
        }
        acc
    }
}

/// One recorded constraint. Mirrors the snarky constraint surface exposed to
/// o1js (`BasicSnarkyConstraint` + `KimchiConstraint`).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum RecordedConstraint {
    Boolean {
        v: LinComb,
    },
    Equal {
        l: LinComb,
        r: LinComb,
    },
    Square {
        v: LinComb,
        square: LinComb,
    },
    R1cs {
        a: LinComb,
        b: LinComb,
        c: LinComb,
    },
    /// The generic gate `cl·l + cr·r + co·o + m·l·r + c = 0`.
    Generic {
        #[serde(with = "fp_decimal")]
        cl: Fp,
        l: LinComb,
        #[serde(with = "fp_decimal")]
        cr: Fp,
        r: LinComb,
        #[serde(with = "fp_decimal")]
        co: Fp,
        o: LinComb,
        #[serde(with = "fp_decimal")]
        m: Fp,
        #[serde(with = "fp_decimal")]
        c: Fp,
    },
    /// Full Poseidon permutation rows: the sponge states per round plus the
    /// final state.
    Poseidon {
        states: Vec<Vec<LinComb>>,
        last: Vec<LinComb>,
    },
}

/// A replayable application circuit.
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RecordedCircuit {
    /// Number of witness variables (allocated in order; every `LinComb`
    /// index must be below this).
    pub aux_count: u32,
    /// The linear combinations whose values form the application state
    /// bound by the Pickles accumulator digest.
    pub output: Vec<LinComb>,
    pub constraints: Vec<RecordedConstraint>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecordedCircuitError {
    /// A `LinComb` references a variable index at or above `aux_count`.
    VariableOutOfRange(u32),
    /// A witness was provided with a length other than `aux_count`.
    WrongWitnessLength(usize),
    /// A Poseidon constraint has malformed state dimensions.
    MalformedPoseidon,
}

impl RecordedCircuit {
    pub fn validate(&self) -> Result<(), RecordedCircuitError> {
        let check = |lincomb: &LinComb| match lincomb.max_var() {
            Some(index) if index >= self.aux_count => {
                Err(RecordedCircuitError::VariableOutOfRange(index))
            }
            _ => Ok(()),
        };
        for lincomb in &self.output {
            check(lincomb)?;
        }
        for constraint in &self.constraints {
            match constraint {
                RecordedConstraint::Boolean { v } => check(v)?,
                RecordedConstraint::Equal { l, r } => {
                    check(l)?;
                    check(r)?;
                }
                RecordedConstraint::Square { v, square } => {
                    check(v)?;
                    check(square)?;
                }
                RecordedConstraint::R1cs { a, b, c } => {
                    check(a)?;
                    check(b)?;
                    check(c)?;
                }
                RecordedConstraint::Generic { l, r, o, .. } => {
                    check(l)?;
                    check(r)?;
                    check(o)?;
                }
                RecordedConstraint::Poseidon { states, last } => {
                    if states.iter().any(|state| state.len() != last.len()) {
                        return Err(RecordedCircuitError::MalformedPoseidon);
                    }
                    for lincomb in states.iter().flatten().chain(last.iter()) {
                        check(lincomb)?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Evaluates the output linear combinations over a witness — the
    /// out-of-circuit application state.
    pub fn state(&self, witness: &[Fp]) -> Vec<Fp> {
        self.output
            .iter()
            .map(|lincomb| lincomb.evaluate(witness))
            .collect()
    }
}

/// [`StepApp`] replaying a [`RecordedCircuit`].
#[derive(Clone)]
pub struct RecordedApp {
    pub circuit: RecordedCircuit,
}

impl StepApp for RecordedApp {
    type Witness = Vec<Fp>;

    fn main(
        &self,
        sys: &mut RunState<Fp>,
        witness: Option<&Self::Witness>,
    ) -> SnarkyResult<Vec<FieldVar<Fp>>> {
        let mut vars = Vec::with_capacity(self.circuit.aux_count as usize);
        for index in 0..self.circuit.aux_count as usize {
            let var: FieldVar<Fp> = sys.compute(loc!(), |_| witness.unwrap()[index])?;
            vars.push(var);
        }

        for constraint in &self.circuit.constraints {
            let resolve = |lincomb: &LinComb| lincomb.resolve(&vars);
            match constraint {
                RecordedConstraint::Boolean { v } => sys.add_constraint(
                    snarky::runner::Constraint::BasicSnarkyConstraint(
                        BasicSnarkyConstraint::Boolean(resolve(v)),
                    ),
                    None,
                    loc!(),
                )?,
                RecordedConstraint::Equal { l, r } => sys.add_constraint(
                    snarky::runner::Constraint::BasicSnarkyConstraint(
                        BasicSnarkyConstraint::Equal(resolve(l), resolve(r)),
                    ),
                    None,
                    loc!(),
                )?,
                RecordedConstraint::Square { v, square } => sys.add_constraint(
                    snarky::runner::Constraint::BasicSnarkyConstraint(
                        BasicSnarkyConstraint::Square(resolve(v), resolve(square)),
                    ),
                    None,
                    loc!(),
                )?,
                RecordedConstraint::R1cs { a, b, c } => sys.add_constraint(
                    snarky::runner::Constraint::BasicSnarkyConstraint(
                        BasicSnarkyConstraint::R1CS(resolve(a), resolve(b), resolve(c)),
                    ),
                    None,
                    loc!(),
                )?,
                RecordedConstraint::Generic {
                    cl,
                    l,
                    cr,
                    r,
                    co,
                    o,
                    m,
                    c,
                } => sys.add_constraint(
                    snarky::runner::Constraint::KimchiConstraint(KimchiConstraint::Basic(
                        BasicInput {
                            l: (*cl, resolve(l)),
                            r: (*cr, resolve(r)),
                            o: (*co, resolve(o)),
                            m: *m,
                            c: *c,
                        },
                    )),
                    None,
                    loc!(),
                )?,
                RecordedConstraint::Poseidon { states, last } => sys.add_constraint(
                    snarky::runner::Constraint::KimchiConstraint(KimchiConstraint::Poseidon2(
                        PoseidonInput {
                            states: states
                                .iter()
                                .map(|state| state.iter().map(resolve).collect())
                                .collect(),
                            last: last.iter().map(resolve).collect(),
                        },
                    )),
                    None,
                    loc!(),
                )?,
            }
        }

        Ok(self
            .circuit
            .output
            .iter()
            .map(|lincomb| lincomb.resolve(&vars))
            .collect())
    }

    fn state(&self, witness: &Self::Witness) -> Vec<Fp> {
        self.circuit.state(witness)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecordedProveError {
    Circuit(RecordedCircuitError),
    /// The compiled step circuit's IPA rounds fall outside the supported
    /// dispatch range.
    UnsupportedStepRounds(u32),
    Backend(crate::api::BaseCaseBackendError),
}

impl From<RecordedCircuitError> for RecordedProveError {
    fn from(error: RecordedCircuitError) -> Self {
        Self::Circuit(error)
    }
}

/// Measures the IPA rounds (domain log2) of the step circuit hosting `app`.
fn measure_step_rounds(app: RecordedApp) -> SnarkyResult<u32> {
    use snarky::api::SnarkyCircuit as _;
    let (_, verifier) = crate::api::StepCircuit { app }.compile_to_indexes()?;
    Ok(verifier.index.domain.log_size_of_group)
}

/// The result of proving a recorded circuit: the application state the proof
/// binds and the network-facing proof envelope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordedProof {
    pub app_state: Vec<Fp>,
    pub proof: MinaWrapProof,
}

macro_rules! prove_at_rounds {
    ($app:ident, $witness:ident, $public:ident; $($rounds:literal),+) => {
        match measure_step_rounds($app.clone())
            .map_err(|_| RecordedProveError::UnsupportedStepRounds(0))?
        {
            $(
                $rounds => {
                    let rule = crate::inductive_rule::InductiveRule::new(
                        crate::inductive_rule::RuleId(0),
                        "recorded_base",
                        crate::composition_types::ProofsVerified::N0,
                        $rounds as u8,
                    );
                    let mut backend = crate::api::BaseCaseRuleBackend::<
                        RecordedApp,
                        $rounds,
                        { 13 + $rounds + 9 },
                    >::compile(&rule, $app)
                    .map_err(RecordedProveError::Backend)?;
                    let (_, encoded) = backend
                        .prove_with_mina_encoding(&$public, $witness)
                        .map_err(RecordedProveError::Backend)?;
                    Ok(encoded)
                }
            )+
            rounds => Err(RecordedProveError::UnsupportedStepRounds(rounds)),
        }
    };
}

/// Compiles and proves a recorded circuit through the base-case Pickles
/// pipeline (two-pass wrap VK). The step circuit's domain is measured first
/// so the right monomorphized backend is selected.
pub fn prove_recorded_base_case(
    circuit: RecordedCircuit,
    witness: Vec<Fp>,
) -> Result<RecordedProof, RecordedProveError> {
    circuit.validate()?;
    if witness.len() != circuit.aux_count as usize {
        return Err(RecordedProveError::Circuit(
            RecordedCircuitError::WrongWitnessLength(witness.len()),
        ));
    }
    let app_state = circuit.state(&witness);
    let app = RecordedApp { circuit };
    let public = app_state.clone();
    let proof = prove_at_rounds!(app, witness, public; 9, 10, 11, 12, 13, 14, 15, 16)?;
    Ok(RecordedProof { app_state, proof })
}
