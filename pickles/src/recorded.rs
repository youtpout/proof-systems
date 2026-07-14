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
    #[serde(
        default,
        skip_serializing_if = "Vec::is_empty",
        with = "fp_decimal::terms"
    )]
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
    EcScale {
        rounds: Vec<RecordedScaleRound>,
    },
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
    RangeCheck {
        rows: Vec<Vec<LinComb>>,
    },
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
    Lookup {
        row: Vec<LinComb>,
    },
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
            &self.xt,
            &self.yt,
            &self.xp,
            &self.yp,
            &self.n_acc,
            &self.xr,
            &self.yr,
            &self.s1,
            &self.s3,
            &self.b1,
            &self.b2,
            &self.b3,
            &self.b4,
            &self.inv,
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
    MalformedRow { expected: usize, actual: usize },
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
                    for lincomb in rounds
                        .iter()
                        .flat_map(RecordedEndoscaleScalarRound::lincombs)
                    {
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
                RecordedConstraint::R1cs { a, b, c } => {
                    sys.add_constraint(
                        snarky::runner::Constraint::BasicSnarkyConstraint(
                            BasicSnarkyConstraint::R1CS(resolve(a), resolve(b), resolve(c)),
                        ),
                        None,
                        loc!(),
                    )?
                }
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
                    snarky::runner::Constraint::KimchiConstraint(KimchiConstraint::EcAddComplete(
                        EcAddCompleteInput {
                            p1: (resolve(&p1.0), resolve(&p1.1)),
                            p2: (resolve(&p2.0), resolve(&p2.1)),
                            p3: (resolve(&p3.0), resolve(&p3.1)),
                            inf: resolve(inf),
                            same_x: resolve(same_x),
                            slope: resolve(slope),
                            inf_z: resolve(inf_z),
                            x21_inv: resolve(x21_inv),
                        },
                    )),
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
    // Proofs are made over the full Tick SRS (2^16), so the IPA round count
    // is fixed; this only checks that the circuit's domain fits.
    let domain_log2 = crate::api::StepCircuit { app }.domain_log2()?;
    assert!(
        domain_log2 as usize <= crate::common::TICK_ROUNDS,
        "recorded circuit domain 2^{domain_log2} exceeds the Tick SRS"
    );
    Ok(crate::common::TICK_ROUNDS as u32)
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
                        { 13 + $rounds + 11 },
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
    let proof = prove_at_rounds!(app, witness, public; 16)?;
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

/// The result of proving a recorded circuit through a stable recursive N1
/// chain. This is the envelope of the final wrap proof plus the final
/// same-field reduced messages needed for standalone verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordedStableN1Proof {
    pub app_state: Vec<Fp>,
    pub proof: MinaWrapProof,
    pub challenge_polynomial_commitment: (Fp, Fp),
    pub old_bulletproof_challenges: Vec<Fp>,
    pub dlog_plonk_index: Vec<(Fp, Fp)>,
    pub stable_cycles: usize,
}

/// The result of proving a recorded width-2 recursive step (`N2`) over two
/// recorded base proofs. The public `app_state` is supplied by the caller and
/// bound by the recursive digest together with both verified previous proofs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordedN2Proof {
    pub app_state: Vec<Fp>,
    pub proof: MinaWrapProof,
    pub challenge_polynomial_commitments: [(Fp, Fp); 2],
    pub old_bulletproof_challenges: [Vec<Fp>; 2],
    pub dlog_plonk_index: Vec<(Fp, Fp)>,
}

/// Wrap proofs are made over the full Tock SRS (2^15), so their IPA round
/// count is fixed regardless of the wrap circuit's domain.
const RECORDED_BASE_WRAP_ROUNDS: usize = crate::common::TOCK_ROUNDS;
/// Step proofs (including recursive steps) are made over the full Tick SRS
/// (2^16).
const RECORDED_N1_STEP_ROUNDS: usize = crate::common::TICK_ROUNDS;
const RECORDED_N1_STEP_STMT_LEN: usize =
    crate::recursive_step::width1_step_statement_len(RECORDED_BASE_WRAP_ROUNDS);
const RECORDED_N1_WRAP_STMT_LEN: usize = 13 + RECORDED_N1_STEP_ROUNDS + 11;
// The stable step statement length depends on the rounds of the *wrap*
// proof it verifies (always the full Tock SRS now).
const RECORDED_STABLE_N1_STEP_STMT_LEN: usize =
    crate::recursive_step::width1_step_statement_len(RECORDED_BASE_WRAP_ROUNDS);
const RECORDED_STABLE_N1_WRAP_STMT_LEN: usize = 13 + RECORDED_N1_STEP_ROUNDS + 11;
const RECORDED_N2_STEP_ROUNDS: usize = crate::common::TICK_ROUNDS;
const RECORDED_N2_STEP_STMT_LEN: usize =
    crate::recursive_step::step_statement_len(2, RECORDED_BASE_WRAP_ROUNDS);
const RECORDED_N2_WRAP_STMT_LEN: usize = 13 + RECORDED_N2_STEP_ROUNDS + 11;

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
                        { 13 + $rounds + 11 },
                        RECORDED_N1_STEP_STMT_LEN,
                        RECORDED_N1_WRAP_STMT_LEN,
                    >::compile(&rule)
                    .map_err(RecordedProveError::RecursiveBackend)?;
                    let base = crate::api::prove_base_case_two_pass::<
                        RecordedApp,
                        $rounds,
                        { 13 + $rounds + 11 },
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
    prove_n1_at_rounds!(app, witness, public; 16)
}

macro_rules! prove_stable_n1_at_rounds {
    ($app:ident, $witness:ident, $public:ident, $additional_stable_cycles:ident; $($rounds:literal),+) => {
        match measure_step_rounds($app.clone())
            .map_err(|_| RecordedProveError::UnsupportedStepRounds(0))?
        {
            $(
                $rounds => {
                    let base = crate::api::prove_base_case_two_pass::<
                        RecordedApp,
                        $rounds,
                        { 13 + $rounds + 11 },
                    >($app, $witness);
                    let proof = crate::recursive_step::prove_direct_n1_stable_cycles_with_real_vk::<
                        RecordedApp,
                        $rounds,
                        RECORDED_BASE_WRAP_ROUNDS,
                        RECORDED_N1_STEP_ROUNDS,
                        { 13 + $rounds + 11 },
                        RECORDED_N1_STEP_STMT_LEN,
                        RECORDED_N1_WRAP_STMT_LEN,
                        RECORDED_STABLE_N1_STEP_STMT_LEN,
                        RECORDED_STABLE_N1_WRAP_STMT_LEN,
                    >(&base, $public.clone(), $additional_stable_cycles);
                    let encoded = proof
                        .to_mina_network_proof()
                        .map_err(RecordedProveError::RecursiveBackend)?;
                    let [challenge_polynomial_commitment] = proof.final_accumulators();
                    let [old_bulletproof_challenges] = proof.final_challenges();
                    Ok(RecordedStableN1Proof {
                        app_state: $public.clone(),
                        proof: encoded,
                        challenge_polynomial_commitment,
                        old_bulletproof_challenges,
                        dlog_plonk_index: proof.final_step_vk_pts().to_vec(),
                        stable_cycles: proof.stable_cycles.len(),
                    })
                }
            )+
            rounds => Err(RecordedProveError::UnsupportedStepRounds(rounds)),
        }
    };
}

/// Proves a recorded circuit through the base-case pipeline and then through
/// a stable recursive N1 chain. `additional_stable_cycles = 0` still proves
/// the first stable transition after the initial N1 cycle; larger values append
/// repeated stable step→wrap cycles.
pub fn prove_recorded_stable_n1(
    circuit: RecordedCircuit,
    witness: Vec<Fp>,
    additional_stable_cycles: usize,
) -> Result<RecordedStableN1Proof, RecordedProveError> {
    circuit.validate()?;
    if witness.len() != circuit.aux_count as usize {
        return Err(RecordedProveError::Circuit(
            RecordedCircuitError::WrongWitnessLength(witness.len()),
        ));
    }
    let app_state = circuit.state(&witness);
    let app = RecordedApp { circuit };
    let public = app_state;
    prove_stable_n1_at_rounds!(
        app,
        witness,
        public,
        additional_stable_cycles;
        9, 10, 11, 12, 13, 14, 15, 16
    )
}

macro_rules! prove_n2_at_rounds {
    ($app:ident, $first_witness:ident, $second_witness:ident, $first_state:ident, $second_state:ident, $public:ident; $($rounds:literal),+) => {
        match measure_step_rounds($app.clone())
            .map_err(|_| RecordedProveError::UnsupportedStepRounds(0))?
        {
            $(
                $rounds => {
                    let rule = crate::inductive_rule::InductiveRule::new(
                        crate::inductive_rule::RuleId(2),
                        "recorded_n2",
                        crate::composition_types::ProofsVerified::N2,
                        RECORDED_N2_STEP_ROUNDS as u8,
                    );
                    let mut backend = crate::recursive_step::DirectN2Backend::<
                        RecordedApp,
                        $rounds,
                        RECORDED_BASE_WRAP_ROUNDS,
                        { 13 + $rounds + 11 },
                        RECORDED_N1_STEP_STMT_LEN,
                        RECORDED_N2_STEP_STMT_LEN,
                        RECORDED_N2_STEP_ROUNDS,
                        RECORDED_N2_WRAP_STMT_LEN,
                    >::compile(&rule)
                    .map_err(RecordedProveError::RecursiveBackend)?;
                    let first_base = crate::api::prove_base_case_two_pass::<
                        RecordedApp,
                        $rounds,
                        { 13 + $rounds + 11 },
                    >($app.clone(), $first_witness);
                    let second_base = crate::api::prove_base_case_two_pass::<
                        RecordedApp,
                        $rounds,
                        { 13 + $rounds + 11 },
                    >($app, $second_witness);
                    let (proof, encoded) = backend
                        .prove_with_mina_encoding(
                            &$public,
                            crate::recursive_step::DirectN2Witness {
                                bases: [first_base, second_base],
                                previous_app_states: [$first_state, $second_state],
                            },
                        )
                        .map_err(RecordedProveError::RecursiveBackend)?;
                    Ok(RecordedN2Proof {
                        app_state: $public.clone(),
                        proof: encoded,
                        challenge_polynomial_commitments: proof.accumulators,
                        old_bulletproof_challenges: proof.challenges,
                        dlog_plonk_index: proof.wrap_vk_pts,
                    })
                }
            )+
            rounds => Err(RecordedProveError::UnsupportedStepRounds(rounds)),
        }
    };
}

/// Proves a true width-2 recorded recursive step (`ProofsVerified::N2`) over
/// two base proofs for the same recorded circuit. `app_state` is the public
/// state of the new recursive proof; this low-level adapter only binds it to
/// the recursive digest, it does not derive an aggregation relation from the
/// two previous states.
pub fn prove_recorded_n2(
    circuit: RecordedCircuit,
    first_witness: Vec<Fp>,
    second_witness: Vec<Fp>,
    app_state: Vec<Fp>,
) -> Result<RecordedN2Proof, RecordedProveError> {
    circuit.validate()?;
    if first_witness.len() != circuit.aux_count as usize {
        return Err(RecordedProveError::Circuit(
            RecordedCircuitError::WrongWitnessLength(first_witness.len()),
        ));
    }
    if second_witness.len() != circuit.aux_count as usize {
        return Err(RecordedProveError::Circuit(
            RecordedCircuitError::WrongWitnessLength(second_witness.len()),
        ));
    }
    let first_state = circuit.state(&first_witness);
    let second_state = circuit.state(&second_witness);
    let app = RecordedApp { circuit };
    let public = app_state;
    prove_n2_at_rounds!(
        app,
        first_witness,
        second_witness,
        first_state,
        second_state,
        public;
        9, 10, 11, 12, 13, 14, 15, 16
    )
}

/// A proof kept alive for recursive chaining. The network envelope is enough
/// for standalone verification, but the next Pickles cycle also needs the
/// full previous step/wrap proofs and their verifier indexes.
pub struct RecordedProofHandle {
    pub app_state: Vec<Fp>,
    pub proof: MinaWrapProof,
    inner: RecordedProofInner,
}

/// Backward-compatible name for callers that only retain base proofs.
pub type RecordedBaseHandle = RecordedProofHandle;

/// A recorded base circuit whose Step and Wrap prover indexes stay alive for
/// repeated proofs. The initial witness is used only to discover and compile
/// the two Pickles indexes; every `prove_keep` call supplies its own witness.
pub struct RecordedCompiledBase {
    circuit: RecordedCircuit,
    compiled: crate::api::CompiledBaseCase<RecordedApp, 16, 40>,
}

impl RecordedCompiledBase {
    pub fn compile(circuit: RecordedCircuit, witness: Vec<Fp>) -> Result<Self, RecordedProveError> {
        circuit.validate()?;
        if witness.len() != circuit.aux_count as usize {
            return Err(RecordedProveError::Circuit(
                RecordedCircuitError::WrongWitnessLength(witness.len()),
            ));
        }
        let app = RecordedApp {
            circuit: circuit.clone(),
        };
        let domain_log2 = measure_step_rounds(app.clone())
            .map_err(|_| RecordedProveError::UnsupportedStepRounds(0))?;
        if domain_log2 != 16 {
            return Err(RecordedProveError::UnsupportedStepRounds(domain_log2));
        }
        Ok(Self {
            circuit,
            compiled: crate::api::CompiledBaseCase::compile(app, witness),
        })
    }

    pub fn prove_keep(
        &mut self,
        witness: Vec<Fp>,
    ) -> Result<RecordedProofHandle, RecordedProveError> {
        if witness.len() != self.circuit.aux_count as usize {
            return Err(RecordedProveError::Circuit(
                RecordedCircuitError::WrongWitnessLength(witness.len()),
            ));
        }
        let app_state = self.circuit.state(&witness);
        let base = self.compiled.prove(witness);
        let proof = base
            .to_mina_network_proof()
            .map_err(RecordedProveError::Backend)?;
        Ok(RecordedProofHandle {
            app_state,
            proof,
            inner: RecordedProofInner::R16(base),
        })
    }
}

/// Reusable indexes for the first N1 transition over a retained base proof.
pub struct RecordedCompiledN1 {
    circuit: RecordedCircuit,
    step_indexes: Option<
        crate::recursive_step::RecursiveStepIndexes<
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
        >,
    >,
    wrap_indexes: Option<
        crate::recursive_step::RecursiveWrapIndexes<
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_N1_WRAP_STMT_LEN,
        >,
    >,
    precomputed: Option<PrecomputedRecordedN1>,
}

struct PrecomputedRecordedN1 {
    witness: Vec<Fp>,
    previous_state: Vec<Fp>,
    previous_proof: crate::api::MinaWrapProof,
    new_state: Vec<Fp>,
    step: crate::recursive_step::RecursiveStepProof<
        16,
        RECORDED_BASE_WRAP_ROUNDS,
        RECORDED_N1_STEP_STMT_LEN,
    >,
    prepared_wrap: crate::recursive_step::PreparedRecursiveWrap<
        RECORDED_N1_STEP_ROUNDS,
        RECORDED_N1_WRAP_STMT_LEN,
    >,
}

impl RecordedCompiledN1 {
    pub fn compile(
        previous: &RecordedProofHandle,
        circuit: RecordedCircuit,
        witness: Vec<Fp>,
    ) -> Result<Self, RecordedProveError> {
        circuit.validate()?;
        if witness.len() != circuit.aux_count as usize {
            return Err(RecordedProveError::Circuit(
                RecordedCircuitError::WrongWitnessLength(witness.len()),
            ));
        }
        let RecordedProofInner::R16(base) = &previous.inner else {
            return Err(RecordedProveError::RecursiveBackend(
                crate::recursive_step::DirectRecursiveBackendError::InvalidProof,
            ));
        };
        let profile = std::env::var_os("PICKLES_PROFILE").is_some();
        let started = std::time::Instant::now();
        let new_state = circuit.state(&witness);
        let compiled_witness = witness.clone();
        let app = RecordedApp {
            circuit: circuit.clone(),
        };
        let main: crate::recursive_step::EmbeddedAppMain =
            std::sync::Arc::new(move |sys| app.main(sys, Some(&witness)));
        let wrap_vk_pts = crate::api::wrap_verification_key_points(&base.wrap_verifier);
        let prepared = crate::recursive_step::prepare_recursive_step_with_state::<
            RecordedApp,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            40,
            RECORDED_N1_STEP_STMT_LEN,
        >(
            base,
            wrap_vk_pts,
            previous.app_state.clone(),
            new_state.clone(),
        );
        let prepared_at = std::time::Instant::now();
        let step_indexes = crate::recursive_step::compile_prepared_recursive_step::<
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
        >(&prepared, Some(main.clone()));
        let step_compiled_at = std::time::Instant::now();
        let (step, step_indexes) = crate::recursive_step::prove_prepared_recursive_step(
            prepared,
            Some(main),
            Some(step_indexes),
        );
        let step_proved_at = std::time::Instant::now();
        let prepared_wrap = crate::recursive_step::prepare_recursive_wrap::<
            RecordedApp,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_ROUNDS,
            40,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N1_WRAP_STMT_LEN,
        >(base, &step);
        let wrap_indexes = crate::recursive_step::compile_prepared_recursive_wrap(&prepared_wrap);
        if profile {
            eprintln!(
                "pickles compile N1: prepare={:?} step_index={:?} step_proof={:?} wrap_index={:?} total={:?}",
                prepared_at - started,
                step_compiled_at - prepared_at,
                step_proved_at - step_compiled_at,
                step_proved_at.elapsed(),
                started.elapsed(),
            );
        }
        Ok(Self {
            circuit,
            step_indexes: Some(step_indexes),
            wrap_indexes: Some(wrap_indexes),
            precomputed: Some(PrecomputedRecordedN1 {
                witness: compiled_witness,
                previous_state: previous.app_state.clone(),
                previous_proof: previous.proof.clone(),
                new_state,
                step,
                prepared_wrap,
            }),
        })
    }

    pub fn prove_keep(
        &mut self,
        previous: &RecordedProofHandle,
        witness: Vec<Fp>,
    ) -> Result<RecordedProofHandle, RecordedProveError> {
        if witness.len() != self.circuit.aux_count as usize {
            return Err(RecordedProveError::Circuit(
                RecordedCircuitError::WrongWitnessLength(witness.len()),
            ));
        }
        let RecordedProofInner::R16(base) = &previous.inner else {
            return Err(RecordedProveError::RecursiveBackend(
                crate::recursive_step::DirectRecursiveBackendError::InvalidProof,
            ));
        };
        if self.precomputed.as_ref().is_some_and(|precomputed| {
            precomputed.witness == witness
                && precomputed.previous_state == previous.app_state
                && precomputed.previous_proof == previous.proof
        }) {
            let precomputed = self.precomputed.take().unwrap();
            let wrap_vk_pts = crate::api::wrap_verification_key_points(&base.wrap_verifier);
            let wrap_indexes = self.wrap_indexes.take().expect("compiled N1 Wrap indexes");
            let (wrap, wrap_indexes) = crate::recursive_step::prove_prepared_recursive_wrap(
                precomputed.prepared_wrap,
                Some(wrap_indexes),
            );
            self.wrap_indexes = Some(wrap_indexes);
            let cycle = crate::recursive_step::RecursiveCycleProof {
                step: precomputed.step,
                wrap,
            };
            let proof = crate::recursive_step::DirectN1Proof::<
                16,
                RECORDED_BASE_WRAP_ROUNDS,
                RECORDED_N1_STEP_ROUNDS,
                RECORDED_N1_STEP_STMT_LEN,
                RECORDED_N1_WRAP_STMT_LEN,
            > {
                cycle,
                wrap_vk_pts,
            };
            let encoded = proof
                .to_mina_network_proof()
                .map_err(RecordedProveError::RecursiveBackend)?;
            return Ok(RecordedProofHandle {
                app_state: precomputed.new_state,
                proof: encoded,
                inner: RecordedProofInner::Recursive(proof.cycle),
            });
        }
        let new_state = self.circuit.state(&witness);
        let app = RecordedApp {
            circuit: self.circuit.clone(),
        };
        let main: crate::recursive_step::EmbeddedAppMain =
            std::sync::Arc::new(move |sys| app.main(sys, Some(&witness)));
        let wrap_vk_pts = crate::api::wrap_verification_key_points(&base.wrap_verifier);
        let prepared = crate::recursive_step::prepare_recursive_step_with_state::<
            RecordedApp,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            40,
            RECORDED_N1_STEP_STMT_LEN,
        >(
            base,
            wrap_vk_pts.clone(),
            previous.app_state.clone(),
            new_state.clone(),
        );
        let step_indexes = self.step_indexes.take().expect("compiled N1 Step indexes");
        let (step, step_indexes) = crate::recursive_step::prove_prepared_recursive_step(
            prepared,
            Some(main),
            Some(step_indexes),
        );
        self.step_indexes = Some(step_indexes);
        let prepared_wrap = crate::recursive_step::prepare_recursive_wrap::<
            RecordedApp,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_ROUNDS,
            40,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N1_WRAP_STMT_LEN,
        >(base, &step);
        let wrap_indexes = self.wrap_indexes.take().expect("compiled N1 Wrap indexes");
        let (wrap, wrap_indexes) =
            crate::recursive_step::prove_prepared_recursive_wrap(prepared_wrap, Some(wrap_indexes));
        self.wrap_indexes = Some(wrap_indexes);
        let cycle = crate::recursive_step::RecursiveCycleProof { step, wrap };
        let proof = crate::recursive_step::DirectN1Proof::<
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N1_WRAP_STMT_LEN,
        > {
            cycle,
            wrap_vk_pts,
        };
        let encoded = proof
            .to_mina_network_proof()
            .map_err(RecordedProveError::RecursiveBackend)?;
        Ok(RecordedProofHandle {
            app_state: new_state,
            proof: encoded,
            inner: RecordedProofInner::Recursive(proof.cycle),
        })
    }
}

impl RecordedProofHandle {
    /// The envelope-only view of the kept proof.
    pub fn to_recorded_proof(&self) -> RecordedProof {
        RecordedProof {
            app_state: self.app_state.clone(),
            proof: self.proof.clone(),
        }
    }

    /// Returns the recursive verification envelope, or `None` for a base
    /// handle that has not entered a recursive cycle yet.
    pub fn to_recorded_n1_proof(&self) -> Option<RecordedN1Proof> {
        let RecordedProofInner::Recursive(cycle) = &self.inner else {
            return None;
        };
        Some(RecordedN1Proof {
            app_state: self.app_state.clone(),
            proof: self.proof.clone(),
            challenge_polynomial_commitment: cycle.step.verified_wrap_accumulator,
            old_bulletproof_challenges: cycle.step.finalized_step_challenges.clone(),
            dlog_plonk_index: cycle.step.messages_for_next_step_vk_pts.clone(),
        })
    }
}

type RecordedRecursiveCycle = crate::recursive_step::RecursiveCycleProof<
    RECORDED_N1_STEP_ROUNDS,
    RECORDED_BASE_WRAP_ROUNDS,
    RECORDED_N1_STEP_ROUNDS,
    RECORDED_N1_STEP_STMT_LEN,
    RECORDED_N1_WRAP_STMT_LEN,
>;

enum RecordedProofInner {
    /// Proofs are always made over the full Tick SRS: 16 IPA rounds,
    /// 40-slot OCaml wrap statement.
    R16(crate::api::BaseCaseProof<RecordedApp, 16, 40>),
    Recursive(RecordedRecursiveCycle),
}

macro_rules! prove_base_keep_at_rounds {
    ($app:ident, $witness:ident, $public:ident; $(($rounds:literal, $variant:ident)),+) => {
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
                        { 13 + $rounds + 11 },
                    >::compile(&rule, $app)
                    .map_err(RecordedProveError::Backend)?;
                    let (base, encoded) = backend
                        .prove_with_mina_encoding(&$public, $witness)
                        .map_err(RecordedProveError::Backend)?;
                    Ok(RecordedProofHandle {
                        app_state: $public,
                        proof: encoded,
                        inner: RecordedProofInner::$variant(base),
                    })
                }
            )+
            rounds => Err(RecordedProveError::UnsupportedStepRounds(rounds)),
        }
    };
}

/// [`prove_recorded_base_case`], but keeps the full base proof alive for
/// recursion: the returned handle can be verified as usual through its
/// envelope and later consumed by [`prove_recorded_n1_over`].
pub fn prove_recorded_base_case_keep(
    circuit: RecordedCircuit,
    witness: Vec<Fp>,
) -> Result<RecordedProofHandle, RecordedProveError> {
    circuit.validate()?;
    if witness.len() != circuit.aux_count as usize {
        return Err(RecordedProveError::Circuit(
            RecordedCircuitError::WrongWitnessLength(witness.len()),
        ));
    }
    let app_state = circuit.state(&witness);
    let app = RecordedApp { circuit };
    let public = app_state;
    prove_base_keep_at_rounds!(app, witness, public;
        (16, R16))
}

macro_rules! prove_n1_over_keep_at_rounds {
    ($handle:ident, $main:ident, $new_state:ident; $(($rounds:literal, $variant:ident)),+) => {
        match &$handle.inner {
            $(
                RecordedProofInner::$variant(base) => {
                    let wrap_vk_pts =
                        crate::api::wrap_verification_key_points(&base.wrap_verifier);
                    let cycle =
                        crate::recursive_step::prove_first_recursive_cycle_with_real_vk_and_app::<
                            RecordedApp,
                            $rounds,
                            RECORDED_BASE_WRAP_ROUNDS,
                            RECORDED_N1_STEP_ROUNDS,
                            { 13 + $rounds + 11 },
                            RECORDED_N1_STEP_STMT_LEN,
                            RECORDED_N1_WRAP_STMT_LEN,
                        >(
                            base,
                            $handle.app_state.clone(),
                            Some(($main, $new_state.clone())),
                        );
                    let proof =
                        crate::recursive_step::DirectN1Proof::<
                            $rounds,
                            RECORDED_BASE_WRAP_ROUNDS,
                            RECORDED_N1_STEP_ROUNDS,
                            RECORDED_N1_STEP_STMT_LEN,
                            RECORDED_N1_WRAP_STMT_LEN,
                        > { cycle, wrap_vk_pts };
                    let encoded = proof
                        .to_mina_network_proof()
                        .map_err(RecordedProveError::RecursiveBackend)?;
                    Ok(RecordedProofHandle {
                        app_state: $new_state,
                        proof: encoded,
                        inner: RecordedProofInner::Recursive(proof.cycle),
                    })
                }
            )+
            RecordedProofInner::Recursive(previous) => {
                let cycle = crate::recursive_step::prove_next_recursive_cycle_with_real_vk_and_app::<
                    RECORDED_N1_STEP_ROUNDS,
                    RECORDED_BASE_WRAP_ROUNDS,
                    RECORDED_N1_STEP_ROUNDS,
                    RECORDED_N1_STEP_STMT_LEN,
                    RECORDED_N1_WRAP_STMT_LEN,
                    RECORDED_BASE_WRAP_ROUNDS,
                    RECORDED_N1_STEP_STMT_LEN,
                    RECORDED_N1_STEP_ROUNDS,
                    RECORDED_N1_WRAP_STMT_LEN,
                >(
                    previous,
                    $handle.app_state.clone(),
                    $new_state.clone(),
                    Some($main),
                );
                let step_domain_log2 =
                    cycle.step.verifier.index.domain.log_size_of_group as u8;
                let encoded = cycle
                    .wrap
                    .to_mina_network_proof(step_domain_log2)
                    .map_err(RecordedProveError::RecursiveBackend)?;
                Ok(RecordedProofHandle {
                    app_state: $new_state,
                    proof: encoded,
                    inner: RecordedProofInner::Recursive(cycle),
                })
            }
        }
    };
}

/// Proves one recursive (`N1`) cycle whose step *runs a new recorded
/// circuit* and verifies a previously kept base proof — the ZkProgram
/// `SelfProof` shape: the proof of call `k` is consumed by call `k + 1`,
/// which may run a different circuit.
///
/// The resulting statement digest binds the *new* circuit's application
/// state, together with the verified proof's accumulator and the base
/// program's wrap verification key (`dlog_plonk_index`) — pass all three to
/// [`crate::verify::verify_side_loaded_with_step_vk`].
///
/// The recursive step circuit (verifier + embedded app) must still fit the
/// fixed 2^{[`RECORDED_N1_STEP_ROUNDS`]} step domain; a larger app panics in
/// the wrap preparation today.
pub fn prove_recorded_n1_over(
    handle: &RecordedProofHandle,
    circuit: RecordedCircuit,
    witness: Vec<Fp>,
) -> Result<RecordedN1Proof, RecordedProveError> {
    let handle = prove_recorded_n1_over_keep(handle, circuit, witness)?;
    Ok(handle
        .to_recorded_n1_proof()
        .expect("N1 proving always returns a recursive handle"))
}

/// [`prove_recorded_n1_over`], retaining the complete recursive proof so the
/// returned handle can be fed into another call without replaying witnesses.
pub fn prove_recorded_n1_over_keep(
    handle: &RecordedProofHandle,
    circuit: RecordedCircuit,
    witness: Vec<Fp>,
) -> Result<RecordedProofHandle, RecordedProveError> {
    circuit.validate()?;
    if witness.len() != circuit.aux_count as usize {
        return Err(RecordedProveError::Circuit(
            RecordedCircuitError::WrongWitnessLength(witness.len()),
        ));
    }
    let new_state = circuit.state(&witness);
    let app = RecordedApp { circuit };
    let main: crate::recursive_step::EmbeddedAppMain =
        std::sync::Arc::new(move |sys| app.main(sys, Some(&witness)));
    prove_n1_over_keep_at_rounds!(handle, main, new_state;
        (16, R16))
}

/// Proves a width-2 recursive step that verifies two retained base proofs and
/// executes a new recorded application circuit in the same step.
pub fn prove_recorded_n2_over_base_handles(
    first: &RecordedProofHandle,
    second: &RecordedProofHandle,
    circuit: RecordedCircuit,
    witness: Vec<Fp>,
) -> Result<RecordedN2Proof, RecordedProveError> {
    circuit.validate()?;
    if witness.len() != circuit.aux_count as usize {
        return Err(RecordedProveError::Circuit(
            RecordedCircuitError::WrongWitnessLength(witness.len()),
        ));
    }
    let (RecordedProofInner::R16(first_base), RecordedProofInner::R16(second_base)) =
        (&first.inner, &second.inner)
    else {
        return Err(RecordedProveError::RecursiveBackend(
            crate::recursive_step::DirectRecursiveBackendError::InvalidProof,
        ));
    };
    let new_state = circuit.state(&witness);
    let app = RecordedApp { circuit };
    let main: crate::recursive_step::EmbeddedAppMain =
        std::sync::Arc::new(move |sys| app.main(sys, Some(&witness)));
    let proof = crate::recursive_step::prove_direct_n2_with_app::<
        RecordedApp,
        RECORDED_N1_STEP_ROUNDS,
        RECORDED_BASE_WRAP_ROUNDS,
        { 13 + RECORDED_N1_STEP_ROUNDS + 11 },
        RECORDED_N1_STEP_STMT_LEN,
        RECORDED_N2_STEP_STMT_LEN,
        RECORDED_N2_STEP_ROUNDS,
        RECORDED_N2_WRAP_STMT_LEN,
    >(
        [first_base, second_base],
        [first.app_state.clone(), second.app_state.clone()],
        new_state.clone(),
        Some(main),
    )
    .map_err(RecordedProveError::RecursiveBackend)?;
    let encoded = proof
        .to_mina_network_proof()
        .map_err(RecordedProveError::RecursiveBackend)?;
    Ok(RecordedN2Proof {
        app_state: new_state,
        proof: encoded,
        challenge_polynomial_commitments: proof.accumulators,
        old_bulletproof_challenges: proof.challenges,
        dlog_plonk_index: proof.wrap_vk_pts,
    })
}

macro_rules! wrap_dump_at_rounds {
    ($app:ident, $witness:ident; $($rounds:literal),+) => {
        match measure_step_rounds($app.clone())
            .map_err(|_| RecordedProveError::UnsupportedStepRounds(0))?
        {
            $(
                $rounds => {
                    // Two passes, like `prove_base_case_two_pass`: the final
                    // wrap circuit embeds the real wrap VK commitments.
                    let bootstrap_points: Vec<(Fp, Fp)> = {
                        use ark_ec::AffineRepr;
                        let g = mina_curves::pasta::Pallas::generator().into_group();
                        (1..=28u64)
                            .map(|i| {
                                let p: mina_curves::pasta::Pallas =
                                    (g * mina_curves::pasta::Fq::from(i)).into();
                                (p.x, p.y)
                            })
                            .collect()
                    };
                    let bootstrap = crate::api::prove_base_case::<RecordedApp, $rounds, { 13 + $rounds + 11 }>(
                        $app.clone(),
                        $witness.clone(),
                        bootstrap_points,
                    );
                    let actual = crate::api::wrap_verification_key_points(&bootstrap.wrap_verifier);
                    let (_, dump) = crate::api::prove_base_case_with_wrap_dump::<
                        RecordedApp,
                        $rounds,
                        { 13 + $rounds + 11 },
                    >($app, $witness, actual);
                    serde_json::to_string(&dump)
                        .map_err(|_| RecordedProveError::UnsupportedStepRounds($rounds))
                }
            )+
            rounds => Err(RecordedProveError::UnsupportedStepRounds(rounds)),
        }
    };
}

/// Serializes the full wrap circuit of a recorded base-case program as
/// `{ public_input_size, gates }` JSON (Fq gates) — the Rust half of the
/// wrap-circuit parity diff against jsoo's `fq_prover_to_json`.
pub fn dump_recorded_wrap_circuit(
    circuit: RecordedCircuit,
    witness: Vec<Fp>,
) -> Result<String, RecordedProveError> {
    circuit.validate()?;
    if witness.len() != circuit.aux_count as usize {
        return Err(RecordedProveError::Circuit(
            RecordedCircuitError::WrongWitnessLength(witness.len()),
        ));
    }
    let app = RecordedApp { circuit };
    wrap_dump_at_rounds!(app, witness; 16)
}
