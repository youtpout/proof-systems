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
    constraint_system::{
        BasicInput, BasicSnarkyConstraint, EcAddCompleteInput, EcEndoscaleInput, EndoscaleRound,
        EndoscaleScalarRound, KimchiConstraint, PoseidonInput, ScaleRound,
    },
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
    /// Complete EC addition: `p3 = p1 + p2` with the exception witnesses.
    EcAddComplete {
        p1: (LinComb, LinComb),
        p2: (LinComb, LinComb),
        p3: (LinComb, LinComb),
        inf: LinComb,
        same_x: LinComb,
        slope: LinComb,
        inf_z: LinComb,
        x21_inv: LinComb,
    },
    /// Variable-base scalar multiplication rounds (VarBaseMul gates).
    EcScale { rounds: Vec<RecordedScaleRound> },
    /// Endomorphism-based scalar multiplication rounds (EndoMul gates).
    EcEndoscale {
        rounds: Vec<RecordedEndoscaleRound>,
        xs: LinComb,
        ys: LinComb,
        n_acc: LinComb,
    },
    /// Endomorphism scalar conversion rounds (EndoMulScalar gates).
    EcEndoscalar {
        rounds: Vec<RecordedEndoscaleScalarRound>,
    },
    /// The 4-row multi-range-check gadget (three 88-bit values); each row
    /// holds 15 variables in column order.
    RangeCheck { rows: Vec<Vec<LinComb>> },
    /// A single 88-bit range-check row: 15 variables in column order
    /// `[v, vp0..vp5, vc0..vc7]`, plus the `compact` coefficient (0 or 1).
    RangeCheck0 {
        row: Vec<LinComb>,
        #[serde(with = "fp_decimal")]
        compact: Fp,
    },
    /// The two rows of the RangeCheck1 gate: current row and next (Zero)
    /// row, each 15 variables in column order.
    RangeCheck1 {
        row: Vec<LinComb>,
        next: Vec<LinComb>,
    },
    /// A lookup row: the 7 variables `[w0..w6]`.
    Lookup { row: Vec<LinComb> },
}

/// One VarBaseMul round (see [`ScaleRound`]).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RecordedScaleRound {
    pub accs: Vec<(LinComb, LinComb)>,
    pub bits: Vec<LinComb>,
    pub ss: Vec<LinComb>,
    pub base: (LinComb, LinComb),
    pub n_prev: LinComb,
    pub n_next: LinComb,
}

/// One EndoMul round (see [`EndoscaleRound`]).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RecordedEndoscaleRound {
    pub xt: LinComb,
    pub yt: LinComb,
    pub xp: LinComb,
    pub yp: LinComb,
    pub n_acc: LinComb,
    pub xr: LinComb,
    pub yr: LinComb,
    pub s1: LinComb,
    pub s3: LinComb,
    pub b1: LinComb,
    pub b2: LinComb,
    pub b3: LinComb,
    pub b4: LinComb,
    pub inv: LinComb,
}

/// One EndoMulScalar round (see [`EndoscaleScalarRound`]).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RecordedEndoscaleScalarRound {
    pub n0: LinComb,
    pub n8: LinComb,
    pub a0: LinComb,
    pub b0: LinComb,
    pub a8: LinComb,
    pub b8: LinComb,
    pub x0: LinComb,
    pub x1: LinComb,
    pub x2: LinComb,
    pub x3: LinComb,
    pub x4: LinComb,
    pub x5: LinComb,
    pub x6: LinComb,
    pub x7: LinComb,
}

impl RecordedScaleRound {
    fn lincombs(&self) -> impl Iterator<Item = &LinComb> {
        self.accs
            .iter()
            .flat_map(|(x, y)| [x, y])
            .chain(self.bits.iter())
            .chain(self.ss.iter())
            .chain([&self.base.0, &self.base.1, &self.n_prev, &self.n_next])
    }
}

impl RecordedEndoscaleRound {
    fn lincombs(&self) -> impl Iterator<Item = &LinComb> {
        [
            &self.xt, &self.yt, &self.xp, &self.yp, &self.n_acc, &self.xr, &self.yr, &self.s1,
            &self.s3, &self.b1, &self.b2, &self.b3, &self.b4, &self.inv,
        ]
        .into_iter()
    }
}

impl RecordedEndoscaleScalarRound {
    fn lincombs(&self) -> impl Iterator<Item = &LinComb> {
        [
            &self.n0, &self.n8, &self.a0, &self.b0, &self.a8, &self.b8, &self.x0, &self.x1,
            &self.x2, &self.x3, &self.x4, &self.x5, &self.x6, &self.x7,
        ]
        .into_iter()
    }
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
    /// A range-check or lookup constraint has the wrong row shape.
    MalformedRow {
        expected: usize,
        actual: usize,
    },
    /// A multi-range-check gadget does not have exactly 4 rows.
    MalformedRangeCheck(usize),
}

impl RecordedCircuit {
    pub fn validate(&self) -> Result<(), RecordedCircuitError> {
        let check = |lincomb: &LinComb| match lincomb.max_var() {
            Some(index) if index >= self.aux_count => {
                Err(RecordedCircuitError::VariableOutOfRange(index))
            }
            _ => Ok(()),
        };
        let check_row = |row: &[LinComb], expected: usize| {
            if row.len() == expected {
                Ok(())
            } else {
                Err(RecordedCircuitError::MalformedRow {
                    expected,
                    actual: row.len(),
                })
            }
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
                RecordedConstraint::EcAddComplete {
                    p1,
                    p2,
                    p3,
                    inf,
                    same_x,
                    slope,
                    inf_z,
                    x21_inv,
                } => {
                    for lincomb in [
                        &p1.0, &p1.1, &p2.0, &p2.1, &p3.0, &p3.1, inf, same_x, slope, inf_z,
                        x21_inv,
                    ] {
                        check(lincomb)?;
                    }
                }
                RecordedConstraint::EcScale { rounds } => {
                    for lincomb in rounds.iter().flat_map(RecordedScaleRound::lincombs) {
                        check(lincomb)?;
                    }
                }
                RecordedConstraint::EcEndoscale {
                    rounds,
                    xs,
                    ys,
                    n_acc,
                } => {
                    for lincomb in rounds
                        .iter()
                        .flat_map(RecordedEndoscaleRound::lincombs)
                        .chain([xs, ys, n_acc])
                    {
                        check(lincomb)?;
                    }
                }
                RecordedConstraint::EcEndoscalar { rounds } => {
                    for lincomb in rounds.iter().flat_map(RecordedEndoscaleScalarRound::lincombs) {
                        check(lincomb)?;
                    }
                }
                RecordedConstraint::RangeCheck { rows } => {
                    if rows.len() != 4 {
                        return Err(RecordedCircuitError::MalformedRangeCheck(rows.len()));
                    }
                    for row in rows {
                        check_row(row, 15)?;
                        for lincomb in row {
                            check(lincomb)?;
                        }
                    }
                }
                RecordedConstraint::RangeCheck0 { row, .. } => {
                    check_row(row, 15)?;
                    for lincomb in row {
                        check(lincomb)?;
                    }
                }
                RecordedConstraint::RangeCheck1 { row, next } => {
                    for row in [row, next] {
                        check_row(row, 15)?;
                        for lincomb in row {
                            check(lincomb)?;
                        }
                    }
                }
                RecordedConstraint::Lookup { row } => {
                    check_row(row, 7)?;
                    for lincomb in row {
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
                RecordedConstraint::EcAddComplete {
                    p1,
                    p2,
                    p3,
                    inf,
                    same_x,
                    slope,
                    inf_z,
                    x21_inv,
                } => sys.add_constraint(
                    snarky::runner::Constraint::KimchiConstraint(
                        KimchiConstraint::EcAddComplete(EcAddCompleteInput {
                            p1: (resolve(&p1.0), resolve(&p1.1)),
                            p2: (resolve(&p2.0), resolve(&p2.1)),
                            p3: (resolve(&p3.0), resolve(&p3.1)),
                            inf: resolve(inf),
                            same_x: resolve(same_x),
                            slope: resolve(slope),
                            inf_z: resolve(inf_z),
                            x21_inv: resolve(x21_inv),
                        }),
                    ),
                    None,
                    loc!(),
                )?,
                RecordedConstraint::EcScale { rounds } => sys.add_constraint(
                    snarky::runner::Constraint::KimchiConstraint(KimchiConstraint::EcScale(
                        rounds
                            .iter()
                            .map(|round| ScaleRound {
                                accs: round
                                    .accs
                                    .iter()
                                    .map(|(x, y)| (resolve(x), resolve(y)))
                                    .collect(),
                                bits: round.bits.iter().map(resolve).collect(),
                                ss: round.ss.iter().map(resolve).collect(),
                                base: (resolve(&round.base.0), resolve(&round.base.1)),
                                n_prev: resolve(&round.n_prev),
                                n_next: resolve(&round.n_next),
                            })
                            .collect(),
                    )),
                    None,
                    loc!(),
                )?,
                RecordedConstraint::EcEndoscale {
                    rounds,
                    xs,
                    ys,
                    n_acc,
                } => sys.add_constraint(
                    snarky::runner::Constraint::KimchiConstraint(KimchiConstraint::EcEndoscale(
                        EcEndoscaleInput {
                            state: rounds
                                .iter()
                                .map(|round| EndoscaleRound {
                                    xt: resolve(&round.xt),
                                    yt: resolve(&round.yt),
                                    xp: resolve(&round.xp),
                                    yp: resolve(&round.yp),
                                    n_acc: resolve(&round.n_acc),
                                    xr: resolve(&round.xr),
                                    yr: resolve(&round.yr),
                                    s1: resolve(&round.s1),
                                    s3: resolve(&round.s3),
                                    b1: resolve(&round.b1),
                                    b2: resolve(&round.b2),
                                    b3: resolve(&round.b3),
                                    b4: resolve(&round.b4),
                                    inv: resolve(&round.inv),
                                })
                                .collect(),
                            xs: resolve(xs),
                            ys: resolve(ys),
                            n_acc: resolve(n_acc),
                        },
                    )),
                    None,
                    loc!(),
                )?,
                RecordedConstraint::EcEndoscalar { rounds } => sys.add_constraint(
                    snarky::runner::Constraint::KimchiConstraint(KimchiConstraint::EcEndoscalar(
                        rounds
                            .iter()
                            .map(|round| EndoscaleScalarRound {
                                n0: resolve(&round.n0),
                                n8: resolve(&round.n8),
                                a0: resolve(&round.a0),
                                b0: resolve(&round.b0),
                                a8: resolve(&round.a8),
                                b8: resolve(&round.b8),
                                x0: resolve(&round.x0),
                                x1: resolve(&round.x1),
                                x2: resolve(&round.x2),
                                x3: resolve(&round.x3),
                                x4: resolve(&round.x4),
                                x5: resolve(&round.x5),
                                x6: resolve(&round.x6),
                                x7: resolve(&round.x7),
                            })
                            .collect(),
                    )),
                    None,
                    loc!(),
                )?,
                RecordedConstraint::RangeCheck { rows } => sys.add_constraint(
                    snarky::runner::Constraint::KimchiConstraint(KimchiConstraint::RangeCheck(
                        rows.iter()
                            .map(|row| row.iter().map(resolve).collect())
                            .collect(),
                    )),
                    None,
                    loc!(),
                )?,
                RecordedConstraint::RangeCheck0 { row, compact } => sys.add_constraint(
                    snarky::runner::Constraint::KimchiConstraint(KimchiConstraint::RangeCheck0(
                        row.iter().map(resolve).collect(),
                        *compact,
                    )),
                    None,
                    loc!(),
                )?,
                RecordedConstraint::RangeCheck1 { row, next } => sys.add_constraint(
                    snarky::runner::Constraint::KimchiConstraint(KimchiConstraint::RangeCheck1(
                        row.iter().map(resolve).collect(),
                        next.iter().map(resolve).collect(),
                    )),
                    None,
                    loc!(),
                )?,
                RecordedConstraint::Lookup { row } => sys.add_constraint(
                    snarky::runner::Constraint::KimchiConstraint(KimchiConstraint::Lookup(
                        row.iter().map(resolve).collect(),
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
    RecursiveBackend(crate::recursive_step::DirectRecursiveBackendError),
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

/// The result of proving one recursive (`N1`) cycle over a recorded circuit:
/// the wrap proof plus the recursion messages a standalone verifier needs to
/// rebuild the statement's messages-for-next-step digest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordedN1Proof {
    pub app_state: Vec<Fp>,
    pub proof: MinaWrapProof,
    /// The verified wrap proof's challenge-polynomial commitment.
    pub challenge_polynomial_commitment: (Fp, Fp),
    /// The finalized bulletproof challenges of the verified wrap proof.
    pub old_bulletproof_challenges: Vec<Fp>,
    /// The base program's wrap verification-key commitments — the
    /// `dlog_plonk_index` bound by the digest (pass to
    /// [`crate::verify::verify_side_loaded_with_step_vk`]).
    pub dlog_plonk_index: Vec<(Fp, Fp)>,
}

/// The wrap circuit of the base (`N0`) program always compiles to a 2^13
/// domain (`wrap_domains(0)`).
const RECORDED_BASE_WRAP_ROUNDS: usize = 13;
/// The recursive step circuit (finalize + incremental verification of the
/// base wrap proof) compiles to a 2^14 domain, independent of the app.
const RECORDED_N1_STEP_ROUNDS: usize = 14;
const RECORDED_N1_STEP_STMT_LEN: usize =
    crate::recursive_step::width1_step_statement_len(RECORDED_BASE_WRAP_ROUNDS);
const RECORDED_N1_WRAP_STMT_LEN: usize = 13 + RECORDED_N1_STEP_ROUNDS + 9;

macro_rules! prove_n1_at_rounds {
    ($app:ident, $witness:ident, $public:ident; $($rounds:literal),+) => {
        match measure_step_rounds($app.clone())
            .map_err(|_| RecordedProveError::UnsupportedStepRounds(0))?
        {
            $(
                $rounds => {
                    let rule = crate::inductive_rule::InductiveRule::new(
                        crate::inductive_rule::RuleId(1),
                        "recorded_n1",
                        crate::composition_types::ProofsVerified::N1,
                        RECORDED_N1_STEP_ROUNDS as u8,
                    );
                    let mut backend = crate::recursive_step::DirectN1Backend::<
                        RecordedApp,
                        $rounds,
                        RECORDED_BASE_WRAP_ROUNDS,
                        RECORDED_N1_STEP_ROUNDS,
                        { 13 + $rounds + 9 },
                        RECORDED_N1_STEP_STMT_LEN,
                        RECORDED_N1_WRAP_STMT_LEN,
                    >::compile(&rule)
                    .map_err(RecordedProveError::RecursiveBackend)?;
                    let base = crate::api::prove_base_case_two_pass::<
                        RecordedApp,
                        $rounds,
                        { 13 + $rounds + 9 },
                    >($app, $witness);
                    let (proof, encoded) = backend
                        .prove_with_mina_encoding(
                            &$public,
                            crate::recursive_step::DirectN1Witness { base },
                        )
                        .map_err(RecordedProveError::RecursiveBackend)?;
                    Ok(RecordedN1Proof {
                        app_state: $public.clone(),
                        proof: encoded,
                        challenge_polynomial_commitment: proof
                            .cycle
                            .step
                            .verified_wrap_accumulator,
                        old_bulletproof_challenges: proof
                            .cycle
                            .step
                            .finalized_step_challenges
                            .clone(),
                        dlog_plonk_index: proof.wrap_vk_pts.clone(),
                    })
                }
            )+
            rounds => Err(RecordedProveError::UnsupportedStepRounds(rounds)),
        }
    };
}

/// Proves a recorded circuit through the base-case pipeline, then one
/// recursive (`N1`) cycle over the resulting wrap proof — every check real
/// (`must_verify = true`). Returns the recursive wrap proof and the
/// recursion messages needed for standalone verification.
pub fn prove_recorded_n1(
    circuit: RecordedCircuit,
    witness: Vec<Fp>,
) -> Result<RecordedN1Proof, RecordedProveError> {
    circuit.validate()?;
    if witness.len() != circuit.aux_count as usize {
        return Err(RecordedProveError::Circuit(
            RecordedCircuitError::WrongWitnessLength(witness.len()),
        ));
    }
    let app_state = circuit.state(&witness);
    let app = RecordedApp { circuit };
    let public = app_state;
    prove_n1_at_rounds!(app, witness, public; 9, 10, 11, 12, 13, 14, 15, 16)
}
