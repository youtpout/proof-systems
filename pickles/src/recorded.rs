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
use mina_curves::pasta::{Fp, Pallas, Vesta};
use snarky::{
    constraint_system::{
        BasicInput, BasicSnarkyConstraint, EcAddCompleteInput, EcEndoscaleInput, EndoscaleRound,
        EndoscaleScalarRound, KimchiConstraint, PoseidonInput, ScaleRound,
    },
    loc, FieldVar, RunState, SnarkyResult,
};

use crate::api::{MinaWrapProof, StepApp};

/// Maps an o1js `KimchiGateType` tag (from `Gates.raw`) to the rust kimchi
/// [`GateType`]. o1js's enum omits the four Cairo gates, so tags from
/// `RangeCheck0` up are offset by 4 relative to the rust discriminants — hence
/// the explicit mapping rather than a numeric cast.
fn raw_gate_type(tag: u8) -> Result<kimchi::circuits::gate::GateType, RecordedProveError> {
    use kimchi::circuits::gate::GateType::*;
    Ok(match tag {
        0 => Zero,
        1 => Generic,
        2 => Poseidon,
        3 => CompleteAdd,
        4 => VarBaseMul,
        5 => EndoMul,
        6 => EndoMulScalar,
        7 => Lookup,
        8 => RangeCheck0,
        9 => RangeCheck1,
        10 => ForeignFieldAdd,
        11 => ForeignFieldMul,
        12 => Xor16,
        13 => Rot64,
        other => {
            return Err(RecordedProveError::Program(format!(
                "raw gate: unknown KimchiGateType tag {other}"
            )))
        }
    })
}

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

    pub mod vec {
        use super::*;
        use serde::ser::SerializeSeq;

        pub fn serialize<S: Serializer>(value: &[Fp], serializer: S) -> Result<S::Ok, S::Error> {
            let mut seq = serializer.serialize_seq(Some(value.len()))?;
            for coeff in value {
                seq.serialize_element(&coeff.to_string())?;
            }
            seq.end()
        }

        pub fn deserialize<'de, D: Deserializer<'de>>(
            deserializer: D,
        ) -> Result<Vec<Fp>, D::Error> {
            let raw = Vec::<String>::deserialize(deserializer)?;
            raw.into_iter()
                .map(|coeff| {
                    Fp::from_str(&coeff)
                        .map_err(|_| serde::de::Error::custom("expected a decimal Pasta Fp"))
                })
                .collect()
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
    /// o1js `Snarky.field.truncateToBits16` = OCaml
    /// `Scalar_challenge.to_field_checked'`: emit the `EndoMulScalar` rows for
    /// a `num_bits`-bit range-truncation of `input`, then alias `output` to the
    /// gadget's recomposed value `n` (what `truncateToBits16` returns), so no
    /// extra equality gate is added. Used by every UInt range check; missing it
    /// (the recorder does not hook this native op) left a SmartContract Step
    /// circuit with the whole wiring shifted vs jsoo.
    Endoscalar {
        input: LinComb,
        output: LinComb,
        num_bits: u32,
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
    /// A single `Xor16` gate row: 15 variables in column order
    /// `[in1, in2, out, in1_0..3, in2_0..3, out_0..3]`.
    Xor16 {
        row: Vec<LinComb>,
    },
    /// A single `Rot64` gate row: 15 variables in column order
    /// `[word, rotated, excess, bound_limb0..3, bound_crumb0..7]`, plus the
    /// rotation scalar `2^rot`.
    Rot64 {
        row: Vec<LinComb>,
        #[serde(with = "fp_decimal")]
        two_to_rot: Fp,
    },
    /// A raw gate (o1js `Gates.raw`): the `KimchiGateType` tag, its (padded to
    /// 15) variables, and coefficients. Used e.g. for the trailing `Zero` row
    /// of an XOR chain.
    Raw {
        gate_type: u8,
        row: Vec<LinComb>,
        #[serde(with = "fp_decimal::vec", default)]
        coeffs: Vec<Fp>,
    },
    /// A `ForeignFieldAdd` gate row: 8 variables in column order
    /// `[left0..2, right0..2, field_overflow, carry]`, plus the coefficients
    /// `[modulus0..2, sign]`.
    ForeignFieldAdd {
        row: Vec<LinComb>,
        #[serde(with = "fp_decimal::vec", default)]
        coeffs: Vec<Fp>,
    },
    /// A `ForeignFieldMul` gate: the current row (15 vars) and the trailing
    /// `Zero` row (12 vars), plus the coefficients
    /// `[foreign_field_modulus2, neg_foreign_field_modulus0..2]`.
    ForeignFieldMul {
        curr: Vec<LinComb>,
        next: Vec<LinComb>,
        #[serde(with = "fp_decimal::vec", default)]
        coeffs: Vec<Fp>,
    },
    /// The o1js `DynamicProof.verify(vk)` declaration point: the replay
    /// expands OCaml's side-loaded verification-key witness gadget here
    /// (`Side_loaded.in_circuit` + in-circuit `vk_digest`) and asserts the
    /// digest equals the app's `vk_hash` value. `proof` is the logical
    /// previous-proof index the key belongs to.
    SideLoadedVk {
        proof: u32,
        vk_hash: LinComb,
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
    /// `(dense_index, prev_state_flat_index)` bindings between auxiliary
    /// slots and the previous proofs' statement fields. OCaml hands the same
    /// cvars to the rule's main and to the verification machinery; the
    /// replay uses these to reuse the pre-witnessed statement vars.
    /// Absent (empty) on legacy recordings — the layout heuristic applies.
    #[serde(default)]
    pub previous_state_slots: Vec<(u32, u32)>,
    /// Per previous proof (logical order), the verified proof's own program
    /// width — OCaml's per-tag `max_proofs_verified` (a DynamicProof's
    /// declared bound, a SelfProof's own program width). Absent (empty) on
    /// legacy recordings: every slot falls back to the program's width.
    #[serde(default)]
    pub previous_proof_widths: Vec<u8>,
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
                RecordedConstraint::Endoscalar { input, output, .. } => {
                    check(input)?;
                    check(output)?;
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
                RecordedConstraint::Xor16 { row } | RecordedConstraint::Rot64 { row, .. } => {
                    check_row(row, 15)?;
                    for lincomb in row {
                        check(lincomb)?;
                    }
                }
                RecordedConstraint::Raw { row, .. }
                | RecordedConstraint::ForeignFieldAdd { row, .. } => {
                    for lincomb in row {
                        check(lincomb)?;
                    }
                }
                RecordedConstraint::ForeignFieldMul { curr, next, .. } => {
                    for lincomb in curr.iter().chain(next.iter()) {
                        check(lincomb)?;
                    }
                }
                RecordedConstraint::SideLoadedVk { vk_hash, .. } => check(vk_hash)?,
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

/// The in-circuit side-loaded verification key of one previous-proof slot,
/// witnessed by the APP replay (OCaml `Side_loaded.in_circuit` runs inside
/// the rule's main) and consumed by the same-thread step machinery.
pub(crate) struct SideLoadedVkVars {
    pub index: crate::composition_types::PlonkVerificationKeyEvals<
        snarky::gadgets::curve::Point<Fp>,
    >,
    #[allow(dead_code)]
    pub max_pv_one_hot: Vec<snarky::Boolean<Fp>>,
    #[allow(dead_code)]
    pub domain_one_hot: Vec<snarky::Boolean<Fp>>,
}

std::thread_local! {
    /// Slot-indexed stash bridging the app replay to the per-proof
    /// machinery. One circuit synthesis runs on one thread, and the app
    /// main runs FIRST (app-before-machinery), so the machinery can take
    /// each slot's witnessed key without any struct plumbing.
    pub(crate) static SIDE_LOADED_VK_STASH: std::cell::RefCell<
        std::collections::HashMap<usize, SideLoadedVkVars>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

/// Emits OCaml's `Side_loaded_verification_key.typ` witness + checks and the
/// in-circuit `vk_digest`, returning the witnessed key vars. Row layout
/// (side_loaded_verification_key.ml:349+, one_hot_vector.ml, mina_hash):
/// two one-hot vectors (3 boolean rows + one sum-assert each), 28 points
/// witnessed through `Inner_curve.typ` (2 on-curve rows each), then the
/// digest sponge from the `MinaSideLoadedVk` salted state absorbing the 56
/// coordinates and the packed 6-bit one-hot field.
fn side_loaded_vk_gadget(
    sys: &mut RunState<Fp>,
    child_max_pv: usize,
    vk_hash: FieldVar<Fp>,
) -> SnarkyResult<SideLoadedVkVars> {
    use ark_ec::{AffineRepr, CurveGroup};
    use snarky::gadgets::curve::Point;
    use snarky::Boolean;

    let one_hot = |sys: &mut RunState<Fp>, selected: usize| -> SnarkyResult<Vec<Boolean<Fp>>> {
        let bools = (0..3)
            .map(|j| sys.compute(loc!(), move |_| j == selected))
            .collect::<SnarkyResult<Vec<Boolean<Fp>>>>()?;
        // `Boolean.Assert.exactly_one`: the boolean sum equals one.
        let fields: Vec<FieldVar<Fp>> = bools.iter().map(|b| b.to_field_var()).collect();
        let sum = FieldVar::sum(&fields.iter().collect::<Vec<_>>());
        sum.assert_equals(sys, loc!(), &FieldVar::constant(Fp::from(1u64)))?;
        Ok(bools)
    };
    let max_pv_one_hot = one_hot(sys, child_max_pv)?;
    // `actual_wrap_domain_size` — the wrap domain of a `max_pv` program is
    // `wrap_domains(max_pv)` (13/14/15), i.e. one-hot index == max_pv.
    let domain_one_hot = one_hot(sys, child_max_pv)?;

    // The 28 wrap-index commitments (PlonkVerificationKeyEvals order),
    // witnessed through `Inner_curve.typ` (y² = x³ + 5, two rows per
    // point). Compile-time placeholder values: distinct generator
    // multiples (structure only; the prove path will supply the real key).
    let generator = Pallas::generator().into_group();
    let placeholder = |i: usize| -> (Fp, Fp) {
        let p: Pallas = (generator * mina_curves::pasta::Fq::from(i as u64 + 1)).into();
        (p.x, p.y)
    };
    let mkpt = |sys: &mut RunState<Fp>, p: (Fp, Fp)| -> SnarkyResult<Point<Fp>> {
        let point = Point::new(
            sys.compute(loc!(), move |_| p.0)?,
            sys.compute(loc!(), move |_| p.1)?,
        );
        point.assert_on_curve(sys, loc!(), Fp::from(0u64), Fp::from(5u64))?;
        Ok(point)
    };
    let mut points = Vec::with_capacity(28);
    for i in 0..28 {
        points.push(mkpt(sys, placeholder(i))?);
    }
    let index = crate::composition_types::PlonkVerificationKeyEvals {
        sigma_comm: points[0..7].to_vec(),
        coefficients_comm: points[7..22].to_vec(),
        generic_comm: points[22].clone(),
        psm_comm: points[23].clone(),
        complete_add_comm: points[24].clone(),
        mul_comm: points[25].clone(),
        emul_comm: points[26].clone(),
        endomul_scalar_comm: points[27].clone(),
    };

    // In-circuit `vk_digest`: o1js's `inCircuitVkHash` emits the SALT
    // permutation in circuit too (`Snarky.poseidon.update([0,0,0],
    // [prefix])`, zkprogram.ts:1384-1390), then absorbs the 56 coordinates
    // and the packed one-hot field (`pack_to_fields` puts the packed bits
    // LAST — same layout and values as
    // `SideLoadedVerificationKeyV2::mina_hash`).
    let prefix_field = {
        use ark_ff::PrimeField as _;
        let prefix = b"MinaSideLoadedVk****";
        let mut bytes = [0u8; 32];
        bytes[..prefix.len()].copy_from_slice(prefix);
        Fp::from_le_bytes_mod_order(&bytes)
    };
    let mut sponge = crate::sponge::PoseidonSponge::new();
    sponge.absorb(sys, loc!(), &[FieldVar::constant(prefix_field)]);
    let _ = sponge.squeeze(sys, loc!());
    for point in &points {
        sponge.absorb(sys, loc!(), std::slice::from_ref(&point.x));
        sponge.absorb(sys, loc!(), std::slice::from_ref(&point.y));
    }
    let packed = {
        let mut acc = FieldVar::constant(Fp::from(0u64));
        for bit in max_pv_one_hot.iter().chain(domain_one_hot.iter()) {
            acc = &acc.scale(Fp::from(2u64)) + &bit.to_field_var();
        }
        acc
    };
    sponge.absorb(sys, loc!(), std::slice::from_ref(&packed));
    let digest = sponge.squeeze(sys, loc!());
    digest.assert_equals(sys, loc!(), &vk_hash)?;

    Ok(SideLoadedVkVars {
        index,
        max_pv_one_hot,
        domain_one_hot,
    })
}

impl StepApp for RecordedApp {
    type Witness = Vec<Fp>;

    fn main(
        &self,
        sys: &mut RunState<Fp>,
        witness: Option<&Self::Witness>,
    ) -> SnarkyResult<Vec<FieldVar<Fp>>> {
        self.main_with_previous_app_state(sys, witness, &[])
    }

    fn state(&self, witness: &Self::Witness) -> Vec<Fp> {
        self.circuit.state(witness)
    }
}

impl RecordedApp {
    fn has_program_previous_state_slots(&self, previous_app_state_len: usize) -> bool {
        // The o1js Pickles program recorder flattens the Add rule arguments as
        // one current public input followed by the two-field state of every
        // previous proof. Legacy RecordedCircuit tests describe standalone
        // applications instead and must keep allocating all of their vars.
        self.circuit.output.len() == 2
            && self.circuit.aux_count as usize == 1 + previous_app_state_len
    }

    /// Replays an o1js program rule with the previous proofs' application
    /// states occupying the auxiliary slots immediately after the current
    /// public input. OCaml passes those cvars directly to `main`; allocating
    /// fresh witnesses here would preserve values but split their permutation
    /// classes.
    fn main_with_previous_app_state(
        &self,
        sys: &mut RunState<Fp>,
        witness: Option<&Vec<Fp>>,
        previous_app_state: &[FieldVar<Fp>],
    ) -> SnarkyResult<Vec<FieldVar<Fp>>> {
        // Recorded slot bindings take precedence; the layout heuristic only
        // covers legacy recordings without `previous_state_slots`.
        let slot_map: std::collections::HashMap<usize, usize> = self
            .circuit
            .previous_state_slots
            .iter()
            .map(|&(dense, flat)| (dense as usize, flat as usize))
            .collect();
        SIDE_LOADED_VK_STASH.with(|stash| stash.borrow_mut().clear());
        let reuse_previous = slot_map.is_empty()
            && self.has_program_previous_state_slots(previous_app_state.len());
        let mut vars = Vec::with_capacity(self.circuit.aux_count as usize);
        for index in 0..self.circuit.aux_count as usize {
            let var = if let Some(&flat) = slot_map.get(&index) {
                previous_app_state[flat].clone()
            } else if reuse_previous && index > 0 {
                previous_app_state[index - 1].clone()
            } else {
                sys.compute(loc!(), |_| witness.unwrap()[index])?
            };
            vars.push(var);
        }

        for constraint in &self.circuit.constraints {
            // Endoscalar aliases an existing recorded variable to the gadget's
            // recomposed value, so it must run before the immutable `resolve`
            // borrow below and mutate `vars` directly.
            if let RecordedConstraint::Endoscalar {
                input,
                output,
                num_bits,
            } = constraint
            {
                let input_var = input.resolve(&vars);
                let output_index = output
                    .terms
                    .first()
                    .map(|(_, i)| *i as usize)
                    .expect("endoscalar output must be a single recorded variable");
                let (_a, _b, n) = crate::scalar_challenge::scalar_to_field_raw_with_bits(
                    sys,
                    "endoscalar".into(),
                    &input_var,
                    *num_bits as usize,
                )?;
                vars[output_index] = n;
                continue;
            }
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
                RecordedConstraint::Endoscalar { .. } => {
                    unreachable!("Endoscalar is handled before the match")
                }
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
                RecordedConstraint::SideLoadedVk { proof, vk_hash } => {
                    let child_max_pv = self
                        .circuit
                        .previous_proof_widths
                        .get(*proof as usize)
                        .copied()
                        .unwrap_or(0) as usize;
                    let vars = side_loaded_vk_gadget(sys, child_max_pv, resolve(vk_hash))?;
                    SIDE_LOADED_VK_STASH.with(|stash| {
                        stash.borrow_mut().insert(*proof as usize, vars);
                    });
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
                RecordedConstraint::Xor16 { row } => sys.add_constraint(
                    snarky::runner::Constraint::KimchiConstraint(KimchiConstraint::Xor16(
                        row.iter().map(resolve).collect(),
                    )),
                    None,
                    loc!(),
                )?,
                RecordedConstraint::Rot64 { row, two_to_rot } => sys.add_constraint(
                    snarky::runner::Constraint::KimchiConstraint(KimchiConstraint::Rot64(
                        row.iter().map(resolve).collect(),
                        *two_to_rot,
                    )),
                    None,
                    loc!(),
                )?,
                RecordedConstraint::Raw {
                    gate_type,
                    row,
                    coeffs,
                } => {
                    let gate = raw_gate_type(*gate_type).expect("valid KimchiGateType tag");
                    sys.add_constraint(
                        snarky::runner::Constraint::KimchiConstraint(KimchiConstraint::Raw(
                            gate,
                            row.iter().map(resolve).collect(),
                            coeffs.clone(),
                        )),
                        None,
                        loc!(),
                    )?
                }
                RecordedConstraint::ForeignFieldAdd { row, coeffs } => sys.add_constraint(
                    snarky::runner::Constraint::KimchiConstraint(KimchiConstraint::ForeignFieldAdd(
                        row.iter().map(resolve).collect(),
                        coeffs.clone(),
                    )),
                    None,
                    loc!(),
                )?,
                RecordedConstraint::ForeignFieldMul { curr, next, coeffs } => sys.add_constraint(
                    snarky::runner::Constraint::KimchiConstraint(KimchiConstraint::ForeignFieldMul(
                        curr.iter().map(resolve).collect(),
                        next.iter().map(resolve).collect(),
                        coeffs.clone(),
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

}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecordedProveError {
    Circuit(RecordedCircuitError),
    /// The compiled step circuit's IPA rounds fall outside the supported
    /// dispatch range.
    UnsupportedStepRounds(u32),
    Backend(crate::api::BaseCaseBackendError),
    RecursiveBackend(crate::recursive_step::DirectRecursiveBackendError),
    Program(String),
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

const RECORDED_BASE_CACHE_VERSION: u32 = 1;

#[derive(serde::Serialize, serde::Deserialize)]
struct RecordedBaseIndexCache {
    version: u32,
    circuit_digest: [u8; 32],
    index_digest: [u8; 32],
    step_index: Vec<u8>,
    wrap_index: Vec<u8>,
}

fn recorded_circuit_digest(circuit: &RecordedCircuit) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    Sha256::digest(serde_json::to_vec(circuit).expect("recorded circuit serializes")).into()
}

fn recorded_index_digest(step_index: &[u8], wrap_index: &[u8]) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    let mut digest = Sha256::new();
    digest.update(step_index);
    digest.update(wrap_index);
    digest.finalize().into()
}

type RecordedRawStepIndex = kimchi::prover_index::ProverIndex<
    { crate::common::FULL_ROUNDS },
    Vesta,
    poly_commitment::ipa::SRS<Vesta>,
>;
type RecordedRawWrapIndex = kimchi::prover_index::ProverIndex<
    { crate::common::FULL_ROUNDS },
    Pallas,
    poly_commitment::ipa::SRS<Pallas>,
>;

fn restore_step_index(mut index: RecordedRawStepIndex) -> RecordedRawStepIndex {
    let (linearization, powers_of_alpha) =
        kimchi::linearization::expr_linearization(Some(&index.cs.feature_flags), true);
    index.linearization = linearization;
    index.powers_of_alpha = powers_of_alpha;
    index.srs = crate::common::tick_srs(1 << crate::common::TICK_ROUNDS);
    index.verifier_index = None;
    index.verifier_index_digest = None;
    index
}

fn restore_wrap_index(mut index: RecordedRawWrapIndex) -> RecordedRawWrapIndex {
    let (linearization, powers_of_alpha) =
        kimchi::linearization::expr_linearization(Some(&index.cs.feature_flags), true);
    index.linearization = linearization;
    index.powers_of_alpha = powers_of_alpha;
    index.srs = crate::common::tock_srs(1 << crate::common::TOCK_ROUNDS);
    index.verifier_index = None;
    index.verifier_index_digest = None;
    index
}

/// A recorded base circuit whose Step and Wrap prover indexes stay alive for
/// repeated proofs. The initial witness is used only to discover and compile
/// the two Pickles indexes; every `prove_keep` call supplies its own witness.
pub struct RecordedCompiledBase {
    circuit: RecordedCircuit,
    compiled: crate::api::CompiledBaseCase<RecordedApp, 16, 40>,
}

impl RecordedCompiledBase {
    pub fn cache_key(circuit: &RecordedCircuit) -> String {
        let digest = recorded_circuit_digest(circuit);
        let hex = digest
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        format!("recorded-base-v{RECORDED_BASE_CACHE_VERSION}-{hex}")
    }

    pub fn to_cache_bytes(&self) -> Result<Vec<u8>, String> {
        let step = self
            .compiled
            .step_indexes
            .as_ref()
            .ok_or_else(|| "compiled Step index is temporarily in use".to_string())?;
        let wrap = self
            .compiled
            .wrap_indexes
            .as_ref()
            .ok_or_else(|| "compiled Wrap index is temporarily in use".to_string())?;
        let step_index = rmp_serde::to_vec(&step.0.index).map_err(|err| err.to_string())?;
        let wrap_index = rmp_serde::to_vec(&wrap.0.index).map_err(|err| err.to_string())?;
        let cache = RecordedBaseIndexCache {
            version: RECORDED_BASE_CACHE_VERSION,
            circuit_digest: recorded_circuit_digest(&self.circuit),
            index_digest: recorded_index_digest(&step_index, &wrap_index),
            step_index,
            wrap_index,
        };
        rmp_serde::to_vec(&cache).map_err(|err| err.to_string())
    }

    pub fn from_cache_bytes(
        circuit: RecordedCircuit,
        witness: Vec<Fp>,
        bytes: &[u8],
    ) -> Result<Self, String> {
        circuit.validate().map_err(|err| format!("{err:?}"))?;
        if witness.len() != circuit.aux_count as usize {
            return Err(format!("wrong witness length: {}", witness.len()));
        }
        let cache: RecordedBaseIndexCache =
            rmp_serde::from_slice(bytes).map_err(|err| err.to_string())?;
        if cache.version != RECORDED_BASE_CACHE_VERSION
            || cache.circuit_digest != recorded_circuit_digest(&circuit)
        {
            return Err("cached indexes belong to a different circuit or version".into());
        }
        if cache.index_digest != recorded_index_digest(&cache.step_index, &cache.wrap_index) {
            return Err("cached indexes are corrupted".into());
        }
        let step_index: RecordedRawStepIndex =
            rmp_serde::from_slice(&cache.step_index).map_err(|err| err.to_string())?;
        let wrap_index: RecordedRawWrapIndex =
            rmp_serde::from_slice(&cache.wrap_index).map_err(|err| err.to_string())?;
        let app = RecordedApp {
            circuit: circuit.clone(),
        };
        let (step_prover, step_verifier) = snarky::api::ProverIndexWrapper::from_cached_index(
            crate::api::StepCircuit { app: app.clone() },
            0,
            restore_step_index(step_index),
        )?;
        use ark_ec::{AffineRepr, CurveGroup};
        use mina_curves::pasta::Fq;
        let generator = Pallas::generator().into_group();
        let bootstrap_points = (1..=28u64)
            .map(|i| {
                let point = (generator * Fq::from(i)).into_affine();
                (point.x, point.y)
            })
            .collect();
        let built = crate::api::build_base_case::<RecordedApp, 16, 40>(
            app.clone(),
            witness,
            bootstrap_points,
            false,
            Some((step_prover, step_verifier)),
            None,
            Some(restore_wrap_index(wrap_index)),
        );
        let crate::api::BaseCaseBuild::Compiled {
            step_prover,
            step_verifier,
            wrap_prover,
            wrap_verifier,
        } = built
        else {
            return Err("cached base compilation unexpectedly produced a proof".into());
        };
        let wrap_vk_pts = crate::api::wrap_verification_key_points(&wrap_verifier);
        Ok(Self {
            circuit,
            compiled: crate::api::CompiledBaseCase {
                app,
                wrap_vk_pts,
                step_indexes: Some((step_prover, step_verifier)),
                wrap_indexes: Some((wrap_prover, wrap_verifier)),
            },
        })
    }

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
        crate::common::warm_recursion_caches(false);
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

    /// The canonical Mina side-loaded verification key of this circuit:
    /// the bin_prot bytes base64-encoded (what o1js `verificationKey.data`
    /// holds on the jsoo side) and its Mina account-level hash.
    pub fn verification_key_envelope(&self) -> Result<(String, String), RecordedProveError> {
        use base64::prelude::*;
        let step_domain_log2 = self
            .compiled
            .step_indexes
            .as_ref()
            .expect("compiled Step indexes")
            .1
            .index
            .domain
            .log_size_of_group as u8;
        let wrap_verifier = &self
            .compiled
            .wrap_indexes
            .as_ref()
            .expect("compiled Wrap indexes")
            .1;
        let key = crate::side_loaded::SideLoadedVerificationKey::from_wrap_verifier(
            step_domain_log2,
            wrap_verifier,
        )
        .map_err(|err| RecordedProveError::Program(format!("side-loaded key: {err:?}")))?;
        let stable = key.to_stable_v2();
        let base64 = BASE64_STANDARD.encode(
            stable
                .to_bin_prot()
                .map_err(|err| RecordedProveError::Program(format!("VK encoding: {err:?}")))?,
        );
        Ok((base64, stable.mina_hash().to_string()))
    }

    /// Dumps the compiled base-case WRAP circuit gates (structure) in the
    /// `{ public_input_size, gates }` JSON schema — the diagnostic diff target
    /// against jsoo's `fq_prover_to_json` wrap.
    pub fn dump_wrap_circuit_json(&self) -> Result<String, RecordedProveError> {
        #[derive(serde::Serialize)]
        struct Dump {
            public_input_size: usize,
            gates: Vec<kimchi::circuits::gate::CircuitGate<mina_curves::pasta::Fq>>,
            labels: Vec<String>,
        }
        let wrap_prover = &self
            .compiled
            .wrap_indexes
            .as_ref()
            .expect("compiled Wrap indexes")
            .0;
        let dump = Dump {
            public_input_size: wrap_prover.index.cs.public,
            gates: wrap_prover.index.cs.gates.to_vec(),
            labels: wrap_prover.gate_labels().to_vec(),
        };
        serde_json::to_string(&dump)
            .map_err(|err| RecordedProveError::Program(format!("wrap dump: {err}")))
    }

    /// Dumps the STEP (app-logic) circuit gates in the `{ public_input_size,
    /// gates }` schema — for gate-level diff against the jsoo step circuit
    /// (`fp_prover_to_json`). Used to align app gadgets like `hashToGroup`.
    pub fn dump_step_circuit_json(&self) -> Result<String, RecordedProveError> {
        #[derive(serde::Serialize)]
        struct Dump {
            public_input_size: usize,
            gates: Vec<kimchi::circuits::gate::CircuitGate<mina_curves::pasta::Fp>>,
        }
        let step_prover = &self
            .compiled
            .step_indexes
            .as_ref()
            .expect("compiled Step indexes")
            .0;
        let dump = Dump {
            public_input_size: step_prover.index.cs.public,
            gates: step_prover.index.cs.gates.to_vec(),
        };
        serde_json::to_string(&dump)
            .map_err(|err| RecordedProveError::Program(format!("step dump: {err}")))
    }

    /// A proof-SHAPED base handle assembled from the compiled indexes
    /// without running either prover — the compile-time template donor for
    /// the recursive compiles. Its values are protocol-meaningless dummies;
    /// they only ever land in witness slots.
    pub fn donor_handle(&self, witness: &[Fp]) -> Result<RecordedProofHandle, RecordedProveError> {
        let app_state = self.circuit.state(witness);
        let step_verifier = self
            .compiled
            .step_indexes
            .as_ref()
            .expect("compiled Step indexes")
            .1
            .clone();
        let wrap_verifier = self
            .compiled
            .wrap_indexes
            .as_ref()
            .expect("compiled Wrap indexes")
            .1
            .clone();
        let base = crate::recursive_step::dummy_base_case_proof(step_verifier, wrap_verifier);
        let proof = base
            .to_mina_network_proof()
            .map_err(RecordedProveError::Backend)?;
        Ok(RecordedProofHandle {
            app_state,
            proof,
            inner: RecordedProofInner::R16(base),
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

/// Compile-only shared verification key for a non-recursive program (every
/// branch has `proofs_verified == 0`). OCaml `Pickles.compile` gives such a
/// program ONE width-0 wrap that bakes all branch Step domains/VKs, so the
/// zkApp has a single canonical side-loaded verification key. The per-branch
/// width-0 path instead builds one wrap per branch (each baking only its own
/// domain), yielding a different VK per method; this routine produces the
/// shared VK jsoo does.
///
/// Returns `(base64 VK data, Mina account-level hash)`. Proving over this
/// program shape is not wired here — the compile-only zkApp milestone needs
/// only the VK.
pub fn compile_recorded_program_base_shared_vk(
    branches: Vec<RecordedProgramBranch>,
) -> Result<(String, String), RecordedProveError> {
    if branches.is_empty() {
        return Err(RecordedProveError::Program(
            "a program has at least one branch".into(),
        ));
    }
    if branches.iter().any(|branch| branch.proofs_verified != 0) {
        return Err(RecordedProveError::Program(
            "shared width-0 VK requires every branch to be non-recursive".into(),
        ));
    }
    // Compile each branch's Step circuit (the Step verifier index is all the
    // shared wrap needs). `RecordedCompiledBase::compile` also builds a
    // per-branch wrap we discard, but Step compilation dominates and the VK
    // only depends on the Step verifier indexes.
    let bases: Vec<RecordedCompiledBase> = branches
        .into_iter()
        .map(|branch| RecordedCompiledBase::compile(branch.circuit, branch.witness))
        .collect::<Result<_, _>>()?;
    let step_verifiers: Vec<&crate::api::SharedStepVerifierIndex> = bases
        .iter()
        .map(|base| {
            &base
                .compiled
                .step_indexes
                .as_ref()
                .expect("compiled Step indexes")
                .1
                .index
        })
        .collect();
    shared_base_vk_from_step_verifiers(&step_verifiers)
}

/// Builds the shared multi-branch base wrap VK from already-compiled Step
/// verifier indexes. Split out of [`compile_recorded_program_base_shared_vk`]
/// so the batch compile can reuse the Step verifiers it already built instead
/// of recompiling every branch a second time — a double compile that fits in
/// native memory but overruns wasm32's 4 GB linear-memory ceiling and thrashes.
pub fn shared_base_vk_from_bases(
    bases: &[&RecordedCompiledBase],
) -> Result<(String, String), RecordedProveError> {
    let step_verifiers: Vec<&crate::api::SharedStepVerifierIndex> = bases
        .iter()
        .map(|base| {
            &base
                .compiled
                .step_indexes
                .as_ref()
                .expect("compiled Step indexes")
                .1
                .index
        })
        .collect();
    shared_base_vk_from_step_verifiers(&step_verifiers)
}

pub fn shared_base_vk_from_step_verifiers(
    step_verifiers: &[&crate::api::SharedStepVerifierIndex],
) -> Result<(String, String), RecordedProveError> {
    use base64::prelude::*;
    let (_wrap_prover, wrap_verifier) = crate::api::build_shared_base_wrap(step_verifiers);
    // `step_domain_log2` is metadata only (never serialized into the VK); use
    // the largest branch Step domain so it validates against TICK_ROUNDS.
    let step_domain_log2 = step_verifiers
        .iter()
        .map(|svi| svi.domain.log_size_of_group as u8)
        .max()
        .expect("at least one branch");
    let key = crate::side_loaded::SideLoadedVerificationKey::from_wrap_verifier(
        step_domain_log2,
        &wrap_verifier,
    )
    .map_err(|err| RecordedProveError::Program(format!("side-loaded key: {err:?}")))?;
    let stable = key.to_stable_v2();
    let base64 = BASE64_STANDARD.encode(
        stable
            .to_bin_prot()
            .map_err(|err| RecordedProveError::Program(format!("VK encoding: {err:?}")))?,
    );
    Ok((base64, stable.mina_hash().to_string()))
}

/// Debug: the shared wrap's Lagrange basis (one commitment per row of the wrap
/// domain) and its 28 VK commitments — for locating which coefficient-column
/// row diverges from jsoo (`coeff_commitment = sum_R c[R] * L_R`).
#[doc(hidden)]
#[allow(clippy::type_complexity)]
pub fn shared_wrap_lagrange_and_commitments(
    branches: Vec<RecordedProgramBranch>,
) -> Result<
    (
        Vec<(Fp, Fp)>,
        Vec<(Fp, Fp)>,
        Vec<Vec<mina_curves::pasta::Fq>>,
    ),
    RecordedProveError,
> {
    use poly_commitment::SRS as _;
    if branches.is_empty() {
        return Err(RecordedProveError::Program("empty program".into()));
    }
    let bases: Vec<RecordedCompiledBase> = branches
        .into_iter()
        .map(|branch| RecordedCompiledBase::compile(branch.circuit, branch.witness))
        .collect::<Result<_, _>>()?;
    let step_verifiers: Vec<&crate::api::SharedStepVerifierIndex> = bases
        .iter()
        .map(|base| {
            &base
                .compiled
                .step_indexes
                .as_ref()
                .expect("compiled Step indexes")
                .1
                .index
        })
        .collect();
    let (wrap_prover, wrap_verifier) = crate::api::build_shared_base_wrap(&step_verifiers);
    let domain = wrap_prover.index.cs.domain.d1;
    let lagrange = wrap_prover.index.srs.get_lagrange_basis(domain);
    let lagrange_pts: Vec<(Fp, Fp)> = lagrange
        .iter()
        .map(|c| {
            let p = c.chunks[0];
            (p.x, p.y)
        })
        .collect();
    let commitments = crate::api::wrap_verification_key_points(&wrap_verifier);
    // Self-check: reconstruct coefficient columns 1 and 6 from the gate rows as
    // sum_R c_j[R] * L_R and confirm they equal the VK commitments (proves the
    // Lagrange basis / row indexing is right before trusting the row finder).
    if std::env::var_os("COEFF_SELFCHECK").is_some() {
        use ark_ec::{AffineRepr, CurveGroup};
        use ark_ff::Zero;
        let gates = &wrap_prover.index.cs.gates;
        for j in [1usize, 6usize] {
            let mut acc = mina_curves::pasta::Pallas::zero().into_group();
            for (r, g) in gates.iter().enumerate() {
                let c = g
                    .coeffs
                    .get(j)
                    .copied()
                    .unwrap_or(mina_curves::pasta::Fq::from(0u64));
                if !c.is_zero() {
                    let lr = mina_curves::pasta::Pallas::new_unchecked(
                        lagrange_pts[r].0,
                        lagrange_pts[r].1,
                    );
                    acc += lr.into_group() * c;
                }
            }
            let recon = acc.into_affine();
            let vk = commitments[7 + j];
            eprintln!(
                "[selfcheck] coeff[{j}] recon {} VK ({}, {})",
                if (recon.x, recon.y) == vk { "==" } else { "!=" },
                vk.0,
                vk.1
            );
        }
    }
    // Per-row coefficient columns (15 columns), Fq — for the row-diff finder.
    let ncols = 15usize;
    let mut coeff_cols: Vec<Vec<mina_curves::pasta::Fq>> =
        vec![Vec::with_capacity(wrap_prover.index.cs.gates.len()); ncols];
    for g in wrap_prover.index.cs.gates.iter() {
        for j in 0..ncols {
            coeff_cols[j].push(g.coeffs.get(j).copied().unwrap_or(mina_curves::pasta::Fq::from(0u64)));
        }
    }
    Ok((lagrange_pts, commitments, coeff_cols))
}

/// Dumps the SHARED multi-branch wrap circuit gates (structure) in the
/// `{ public_input_size, gates }` schema — for gate-level diff against the jsoo
/// shared wrap (`fq_prover_to_json`).
pub fn dump_shared_base_wrap_json(
    branches: Vec<RecordedProgramBranch>,
) -> Result<String, RecordedProveError> {
    #[derive(serde::Serialize)]
    struct Dump {
        public_input_size: usize,
        gates: Vec<kimchi::circuits::gate::CircuitGate<mina_curves::pasta::Fq>>,
        labels: Vec<String>,
    }
    if branches.is_empty() {
        return Err(RecordedProveError::Program(
            "a program has at least one branch".into(),
        ));
    }
    let bases: Vec<RecordedCompiledBase> = branches
        .into_iter()
        .map(|branch| RecordedCompiledBase::compile(branch.circuit, branch.witness))
        .collect::<Result<_, _>>()?;
    let step_verifiers: Vec<&crate::api::SharedStepVerifierIndex> = bases
        .iter()
        .map(|base| {
            &base
                .compiled
                .step_indexes
                .as_ref()
                .expect("compiled Step indexes")
                .1
                .index
        })
        .collect();
    let (wrap_prover, _wrap_verifier) = crate::api::build_shared_base_wrap(&step_verifiers);
    let dump = Dump {
        public_input_size: wrap_prover.index.cs.public,
        gates: wrap_prover.index.cs.gates.to_vec(),
        labels: wrap_prover.gate_labels().to_vec(),
    };
    serde_json::to_string(&dump)
        .map_err(|err| RecordedProveError::Program(format!("shared wrap dump: {err}")))
}

/// Debug: per-branch Step VK gate-selector commitment infinity status, to tell
/// which kimchi gate types the recorded circuit actually produced (a selector
/// commitment is the point at infinity iff the circuit uses zero gates of that
/// type). Used to compare against jsoo's compiled gate mix.
#[doc(hidden)]
pub fn debug_step_vk_selectors(branches: Vec<RecordedProgramBranch>) -> Result<String, String> {
    use ark_ec::AffineRepr;
    let bases: Vec<RecordedCompiledBase> = branches
        .into_iter()
        .map(|branch| RecordedCompiledBase::compile(branch.circuit, branch.witness))
        .collect::<Result<_, _>>()
        .map_err(|err| format!("{err:?}"))?;
    use ark_ff::{BigInteger, PrimeField};
    // x-coordinate as 32-byte little-endian hex (matches the first 32 bytes of
    // Mina's compressed point encoding in the jsoo step-vk JSON `chunks`).
    let xhex = |c: &poly_commitment::commitment::PolyComm<Vesta>| {
        let p = c.chunks[0];
        if p.is_zero() {
            "INF".to_string()
        } else {
            p.x.into_bigint()
                .to_bytes_le()
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        }
    };
    let mut out = String::new();
    for (i, base) in bases.iter().enumerate() {
        let svi = &base
            .compiled
            .step_indexes
            .as_ref()
            .expect("compiled Step indexes")
            .1
            .index;
        out.push_str(&format!("branch {i} domain=2^{}\n", svi.domain.log_size_of_group));
        out.push_str(&format!("  generic {}\n", xhex(&svi.generic_comm)));
        out.push_str(&format!("  psm {}\n", xhex(&svi.psm_comm)));
        out.push_str(&format!("  complete_add {}\n", xhex(&svi.complete_add_comm)));
        out.push_str(&format!("  mul {}\n", xhex(&svi.mul_comm)));
        out.push_str(&format!("  emul {}\n", xhex(&svi.emul_comm)));
        out.push_str(&format!("  endomul_scalar {}\n", xhex(&svi.endomul_scalar_comm)));
        for (j, c) in svi.sigma_comm.iter().enumerate() {
            out.push_str(&format!("  sigma[{j}] {}\n", xhex(c)));
        }
        for (j, c) in svi.coefficients_comm.iter().enumerate() {
            out.push_str(&format!("  coeff[{j}] {}\n", xhex(c)));
        }
    }
    Ok(out)
}

/// A bare kimchi circuit that runs ONLY the recorded application `main` (no
/// Pickles step machinery), so we can dump the method-level gates and diff
/// them against jsoo's `analyzeMethods` output to find recording infidelities.
struct RecordedAppBare {
    app: RecordedApp,
    witness: Vec<Fp>,
}

impl snarky::api::SnarkyCircuit for RecordedAppBare {
    type Curve = Vesta;
    type Proof = poly_commitment::ipa::OpeningProof<Vesta, { snarky::FULL_ROUNDS }>;
    type PrivateInput = ();
    type PublicInput = ();
    type PublicOutput = ();
    const PREV_CHALLENGES: usize = 0;

    fn srs(size: usize) -> std::sync::Arc<poly_commitment::ipa::SRS<Vesta>> {
        crate::common::tick_srs(size)
    }

    fn circuit(
        &self,
        sys: &mut snarky::runner::RunState<Fp>,
        _public: Self::PublicInput,
        _private: Option<&Self::PrivateInput>,
    ) -> snarky::errors::SnarkyResult<()> {
        self.app.main(sys, Some(&self.witness))?;
        Ok(())
    }
}

/// Debug: the method-level kimchi gates of a single recorded circuit (the
/// application `main` compiled bare), for a gate-by-gate diff against jsoo's
/// `analyzeMethods`.
#[doc(hidden)]
pub fn debug_recorded_method_gates(
    circuit: RecordedCircuit,
    witness: Vec<Fp>,
) -> Result<String, String> {
    use snarky::api::SnarkyCircuit as _;
    let bare = RecordedAppBare {
        app: RecordedApp { circuit },
        witness,
    };
    let (prover, _verifier) = bare
        .compile_to_indexes_with_domain_and_srs(0, Some(crate::common::TICK_ROUNDS as u32))
        .map_err(|err| format!("{err:?}"))?;
    #[derive(serde::Serialize)]
    struct Dump {
        public_input_size: usize,
        gates: Vec<kimchi::circuits::gate::CircuitGate<Fp>>,
    }
    let dump = Dump {
        public_input_size: prover.index.cs.public,
        gates: prover.index.cs.gates.to_vec(),
    };
    serde_json::to_string(&dump).map_err(|err| err.to_string())
}

/// Reusable indexes for the first N1 transition over a retained base proof.
pub struct RecordedCompiledN1 {
    circuit: RecordedCircuit,
    wrap_branches: Vec<crate::api::WrapBranchData>,
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
    stable_step_indexes: Option<
        crate::recursive_step::RecursiveStepIndexes<
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
        >,
    >,
    stable_wrap_indexes: Option<
        crate::recursive_step::RecursiveWrapIndexes<
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_N1_WRAP_STMT_LEN,
        >,
    >,
}

impl RecordedCompiledN1 {
    /// Digest of every compiled index (step, wrap, stable step, stable wrap)
    /// plus the branch VK data. Exposed for the proof-free/bootstrap-proof
    /// equivalence test.
    #[doc(hidden)]
    pub fn index_fingerprint_for_tests(&self) -> Vec<String> {
        type VestaBase = mina_poseidon::sponge::DefaultFqSponge<
            mina_curves::pasta::VestaParameters,
            mina_poseidon::constants::PlonkSpongeConstantsKimchi,
            { snarky::FULL_ROUNDS },
        >;
        type PallasBase = mina_poseidon::sponge::DefaultFqSponge<
            mina_curves::pasta::PallasParameters,
            mina_poseidon::constants::PlonkSpongeConstantsKimchi,
            { snarky::FULL_ROUNDS },
        >;
        let mut out = vec![format!("{:?}", self.wrap_branches)];
        if let Some((_, v)) = &self.step_indexes {
            out.push(format!("{}", v.index.digest::<VestaBase>()));
        }
        if let Some((_, v)) = &self.wrap_indexes {
            out.push(format!("{}", v.index.digest::<PallasBase>()));
        }
        if let Some((_, v)) = &self.stable_step_indexes {
            out.push(format!("{}", v.index.digest::<VestaBase>()));
        }
        if let Some((_, v)) = &self.stable_wrap_indexes {
            out.push(format!("{}", v.index.digest::<PallasBase>()));
        }
        out
    }

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
        crate::common::warm_recursion_caches(true);
        let profile = std::env::var_os("PICKLES_PROFILE").is_some();
        let started = snarky::wasm_instant::Instant::now();
        let new_state = circuit.state(&witness);
        let app = RecordedApp {
            circuit: circuit.clone(),
        };
        let main: crate::recursive_step::EmbeddedAppMain =
            std::sync::Arc::new(move |sys, _previous_app_state| app.main(sys, Some(&witness)));
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
        let prepared_at = snarky::wasm_instant::Instant::now();
        let step_indexes = crate::recursive_step::compile_prepared_recursive_step::<
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
        >(&prepared, Some(main.clone()));
        let step_compiled_at = snarky::wasm_instant::Instant::now();
        let wrap_branches = vec![
            crate::api::WrapBranchData::from_step_verifier(&base.step_verifier.index, 0),
            crate::api::WrapBranchData::from_step_verifier(&step_indexes.1.index, 1),
        ];
        // Compile the Wrap eagerly as part of `compile`, matching
        // `Pickles.compile`: the first call to `prove` must only generate a
        // witness and run the two provers, never discover another index.
        let bootstrap_step =
            crate::recursive_step::dummy_recursive_step_proof(&prepared, step_indexes.1.clone());
        let mut prepared_wrap = crate::recursive_step::prepare_recursive_wrap::<
            RecordedApp,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_ROUNDS,
            40,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N1_WRAP_STMT_LEN,
        >(base, &bootstrap_step);
        prepared_wrap.data.which_branch = 1;
        prepared_wrap.data.branches = wrap_branches.clone();
        let wrap_indexes = crate::recursive_step::compile_prepared_recursive_wrap(&prepared_wrap);
        let bootstrap_wrap = crate::recursive_step::dummy_recursive_wrap_proof(
            &prepared_wrap,
            wrap_indexes.1.clone(),
        );
        // The next prepare asserts `sg == commit(b_poly(chals))` over the
        // challenges materialized in the wrap statement; make the donor
        // consistent (values stay witness-only either way).
        let mut bootstrap_step = bootstrap_step;
        bootstrap_step.proof.proof.sg = crate::dummy::compute_sg(
            bootstrap_step.verifier.index.srs(),
            &crate::recursive_step::statement_challenges_to_field::<RECORDED_N1_STEP_ROUNDS>(
                &prepared_wrap.statement,
            ),
        );
        let bootstrap_cycle = crate::recursive_step::RecursiveCycleProof {
            step: bootstrap_step,
            wrap: bootstrap_wrap,
        };

        // The first transition verifies a base proof. Later transitions
        // verify the stable recursive shape, which has a distinct Step
        // constraint system even though its domains are identical. Compile
        // that second shape now as well so no later prove call discovers an
        // index lazily.
        let stable_wrap_vk =
            crate::api::wrap_verification_key_points(&bootstrap_cycle.wrap.verifier);
        let stable_prepared = crate::recursive_step::prepare_next_recursive_step_with_state::<
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N1_WRAP_STMT_LEN,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
        >(
            &bootstrap_cycle,
            stable_wrap_vk,
            new_state.clone(),
            new_state,
        );
        let stable_step_indexes = crate::recursive_step::compile_prepared_recursive_step::<
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
        >(&stable_prepared, Some(main.clone()));
        let stable_step = crate::recursive_step::dummy_recursive_step_proof(
            &stable_prepared,
            stable_step_indexes.1.clone(),
        );
        let _ = main;
        let stable_prepared_wrap = crate::recursive_step::prepare_next_recursive_wrap::<
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N1_WRAP_STMT_LEN,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_N1_WRAP_STMT_LEN,
        >(&bootstrap_cycle, &stable_step);
        let stable_wrap_indexes =
            crate::recursive_step::compile_prepared_recursive_wrap(&stable_prepared_wrap);
        if profile {
            let step_domain = step_indexes.1.index.domain.log_size_of_group;
            eprintln!(
                "pickles compile N1: domain=2^{step_domain} prepare={:?} step_index={:?} total={:?}",
                prepared_at - started,
                step_compiled_at - prepared_at,
                started.elapsed(),
            );
        }
        Ok(Self {
            circuit,
            wrap_branches,
            step_indexes: Some(step_indexes),
            wrap_indexes: Some(wrap_indexes),
            stable_step_indexes: Some(stable_step_indexes),
            stable_wrap_indexes: Some(stable_wrap_indexes),
        })
    }

    /// The historical N1 compile that ran three bootstrap proofs. Kept as
    /// the reference the proof-free `compile` is tested against.
    #[doc(hidden)]
    pub fn compile_with_bootstrap_proofs_reference(
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
        crate::common::warm_recursion_caches(true);
        let profile = std::env::var_os("PICKLES_PROFILE").is_some();
        let started = snarky::wasm_instant::Instant::now();
        let new_state = circuit.state(&witness);
        let app = RecordedApp {
            circuit: circuit.clone(),
        };
        let main: crate::recursive_step::EmbeddedAppMain =
            std::sync::Arc::new(move |sys, _previous_app_state| app.main(sys, Some(&witness)));
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
        let prepared_at = snarky::wasm_instant::Instant::now();
        let step_indexes = crate::recursive_step::compile_prepared_recursive_step::<
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
        >(&prepared, Some(main.clone()));
        let step_compiled_at = snarky::wasm_instant::Instant::now();
        let wrap_branches = vec![
            crate::api::WrapBranchData::from_step_verifier(&base.step_verifier.index, 0),
            crate::api::WrapBranchData::from_step_verifier(&step_indexes.1.index, 1),
        ];
        // Compile the Wrap eagerly as part of `compile`, matching
        // `Pickles.compile`: the first call to `prove` must only generate a
        // witness and run the two provers, never discover another index.
        let (bootstrap_step, step_indexes) = crate::recursive_step::prove_prepared_recursive_step(
            prepared,
            Some(main.clone()),
            Some(step_indexes),
        );
        let mut prepared_wrap = crate::recursive_step::prepare_recursive_wrap::<
            RecordedApp,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_ROUNDS,
            40,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N1_WRAP_STMT_LEN,
        >(base, &bootstrap_step);
        prepared_wrap.data.which_branch = 1;
        prepared_wrap.data.branches = wrap_branches.clone();
        let wrap_indexes = crate::recursive_step::compile_prepared_recursive_wrap(&prepared_wrap);
        let (bootstrap_wrap, wrap_indexes) =
            crate::recursive_step::prove_prepared_recursive_wrap(prepared_wrap, Some(wrap_indexes));
        let bootstrap_cycle = crate::recursive_step::RecursiveCycleProof {
            step: bootstrap_step,
            wrap: bootstrap_wrap,
        };

        // The first transition verifies a base proof. Later transitions
        // verify the stable recursive shape, which has a distinct Step
        // constraint system even though its domains are identical. Compile
        // that second shape now as well so no later prove call discovers an
        // index lazily.
        let stable_wrap_vk =
            crate::api::wrap_verification_key_points(&bootstrap_cycle.wrap.verifier);
        let stable_prepared = crate::recursive_step::prepare_next_recursive_step_with_state::<
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N1_WRAP_STMT_LEN,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
        >(
            &bootstrap_cycle,
            stable_wrap_vk,
            new_state.clone(),
            new_state,
        );
        let stable_step_indexes = crate::recursive_step::compile_prepared_recursive_step::<
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
        >(&stable_prepared, Some(main.clone()));
        let (stable_step, stable_step_indexes) =
            crate::recursive_step::prove_prepared_recursive_step(
                stable_prepared,
                Some(main),
                Some(stable_step_indexes),
            );
        let stable_prepared_wrap = crate::recursive_step::prepare_next_recursive_wrap::<
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N1_WRAP_STMT_LEN,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_N1_WRAP_STMT_LEN,
        >(&bootstrap_cycle, &stable_step);
        let stable_wrap_indexes =
            crate::recursive_step::compile_prepared_recursive_wrap(&stable_prepared_wrap);
        if profile {
            let step_domain = step_indexes.1.index.domain.log_size_of_group;
            eprintln!(
                "pickles compile N1: domain=2^{step_domain} prepare={:?} step_index={:?} total={:?}",
                prepared_at - started,
                step_compiled_at - prepared_at,
                started.elapsed(),
            );
        }
        Ok(Self {
            circuit,
            wrap_branches,
            step_indexes: Some(step_indexes),
            wrap_indexes: Some(wrap_indexes),
            stable_step_indexes: Some(stable_step_indexes),
            stable_wrap_indexes: Some(stable_wrap_indexes),
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
        let new_state = self.circuit.state(&witness);
        let app = RecordedApp {
            circuit: self.circuit.clone(),
        };
        let main: crate::recursive_step::EmbeddedAppMain =
            std::sync::Arc::new(move |sys, _previous_app_state| app.main(sys, Some(&witness)));
        if let RecordedProofInner::Recursive(previous_cycle) = &previous.inner {
            let stable_wrap_indexes = self
                .stable_wrap_indexes
                .take()
                .expect("compiled stable N1 Wrap indexes");
            let wrap_vk_pts = crate::api::wrap_verification_key_points(&stable_wrap_indexes.1);
            let prepared = crate::recursive_step::prepare_next_recursive_step_with_state::<
                RECORDED_N1_STEP_ROUNDS,
                RECORDED_BASE_WRAP_ROUNDS,
                RECORDED_N1_STEP_ROUNDS,
                RECORDED_N1_STEP_STMT_LEN,
                RECORDED_N1_WRAP_STMT_LEN,
                RECORDED_BASE_WRAP_ROUNDS,
                RECORDED_N1_STEP_STMT_LEN,
            >(
                previous_cycle,
                wrap_vk_pts,
                previous.app_state.clone(),
                new_state.clone(),
            );
            let stable_step_indexes = self
                .stable_step_indexes
                .take()
                .expect("compiled stable N1 Step indexes");
            let (step, stable_step_indexes) = crate::recursive_step::prove_prepared_recursive_step(
                prepared,
                Some(main),
                Some(stable_step_indexes),
            );
            self.stable_step_indexes = Some(stable_step_indexes);
            let prepared_wrap = crate::recursive_step::prepare_next_recursive_wrap::<
                RECORDED_N1_STEP_ROUNDS,
                RECORDED_BASE_WRAP_ROUNDS,
                RECORDED_N1_STEP_ROUNDS,
                RECORDED_N1_STEP_STMT_LEN,
                RECORDED_N1_WRAP_STMT_LEN,
                RECORDED_BASE_WRAP_ROUNDS,
                RECORDED_N1_STEP_STMT_LEN,
                RECORDED_N1_STEP_ROUNDS,
                RECORDED_N1_WRAP_STMT_LEN,
            >(previous_cycle, &step);
            let (wrap, stable_wrap_indexes) = crate::recursive_step::prove_prepared_recursive_wrap(
                prepared_wrap,
                Some(stable_wrap_indexes),
            );
            self.stable_wrap_indexes = Some(stable_wrap_indexes);
            let cycle = crate::recursive_step::RecursiveCycleProof { step, wrap };
            let step_domain_log2 = cycle.step.verifier.index.domain.log_size_of_group as u8;
            let proof = cycle
                .wrap
                .to_mina_network_proof(step_domain_log2)
                .map_err(RecordedProveError::RecursiveBackend)?;
            return Ok(RecordedProofHandle {
                app_state: new_state,
                proof,
                inner: RecordedProofInner::Recursive(cycle),
            });
        }
        let RecordedProofInner::R16(base) = &previous.inner else {
            unreachable!("all recorded proof variants handled")
        };
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
        let mut prepared_wrap = crate::recursive_step::prepare_recursive_wrap::<
            RecordedApp,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_ROUNDS,
            40,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N1_WRAP_STMT_LEN,
        >(base, &step);
        prepared_wrap.data.which_branch = 1;
        prepared_wrap.data.branches = self.wrap_branches.clone();
        let wrap_indexes = self.wrap_indexes.take();
        let (wrap, wrap_indexes) =
            crate::recursive_step::prove_prepared_recursive_wrap(prepared_wrap, wrap_indexes);
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

/// Reusable fixed-width Step and Wrap indexes for an N2 branch. Compilation
/// consumes template proofs only to construct a satisfying compilation
/// witness; later proofs reuse both indexes with the caller's retained
/// proofs and a fresh application witness.
pub struct RecordedCompiledN2 {
    circuit: RecordedCircuit,
    wrap_branches: Vec<crate::api::WrapBranchData>,
    step_indexes: Option<
        crate::recursive_step::RecursiveStepWidth2Indexes<
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N2_STEP_STMT_LEN,
        >,
    >,
    wrap_indexes: Option<
        crate::recursive_step::RecursiveWrapIndexes<
            RECORDED_N2_STEP_ROUNDS,
            RECORDED_N2_WRAP_STMT_LEN,
        >,
    >,
}

impl RecordedCompiledN2 {
    /// See [`RecordedCompiledN1::index_fingerprint_for_tests`].
    #[doc(hidden)]
    pub fn index_fingerprint_for_tests(&self) -> Vec<String> {
        type VestaBase = mina_poseidon::sponge::DefaultFqSponge<
            mina_curves::pasta::VestaParameters,
            mina_poseidon::constants::PlonkSpongeConstantsKimchi,
            { snarky::FULL_ROUNDS },
        >;
        type PallasBase = mina_poseidon::sponge::DefaultFqSponge<
            mina_curves::pasta::PallasParameters,
            mina_poseidon::constants::PlonkSpongeConstantsKimchi,
            { snarky::FULL_ROUNDS },
        >;
        let mut out = vec![format!("{:?}", self.wrap_branches)];
        if let Some((_, v)) = &self.step_indexes {
            out.push(format!("{}", v.index.digest::<VestaBase>()));
        }
        if let Some((_, v)) = &self.wrap_indexes {
            out.push(format!("{}", v.index.digest::<PallasBase>()));
        }
        out
    }

    pub fn compile(
        first: &RecordedProofHandle,
        second: &RecordedProofHandle,
        circuit: RecordedCircuit,
        witness: Vec<Fp>,
    ) -> Result<Self, RecordedProveError> {
        circuit.validate()?;
        if witness.len() != circuit.aux_count as usize {
            return Err(RecordedProveError::Circuit(
                RecordedCircuitError::WrongWitnessLength(witness.len()),
            ));
        }
        crate::common::warm_recursion_caches(true);
        let (RecordedProofInner::R16(first_base), RecordedProofInner::R16(second_base)) =
            (&first.inner, &second.inner)
        else {
            return Err(RecordedProveError::RecursiveBackend(
                crate::recursive_step::DirectRecursiveBackendError::InvalidProof,
            ));
        };
        let app_state = circuit.state(&witness);
        let app = RecordedApp {
            circuit: circuit.clone(),
        };
        let main: crate::recursive_step::EmbeddedAppMain =
            std::sync::Arc::new(move |sys, _previous_app_state| app.main(sys, Some(&witness)));
        let wrap_vk_pts = crate::api::wrap_verification_key_points(&first_base.wrap_verifier);
        let first_prepared = crate::recursive_step::prepare_recursive_step_with_state::<
            RecordedApp,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            40,
            RECORDED_N1_STEP_STMT_LEN,
        >(
            first_base,
            wrap_vk_pts.clone(),
            first.app_state.clone(),
            app_state.clone(),
        );
        let second_prepared = crate::recursive_step::prepare_recursive_step_with_state::<
            RecordedApp,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            40,
            RECORDED_N1_STEP_STMT_LEN,
        >(
            second_base,
            wrap_vk_pts,
            second.app_state.clone(),
            app_state.clone(),
        );
        let prepared = crate::recursive_step::prepare_recursive_step_width2::<
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N2_STEP_STMT_LEN,
        >(first_prepared, second_prepared, app_state);
        let step_indexes = crate::recursive_step::compile_prepared_recursive_step_width2::<
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N2_STEP_STMT_LEN,
        >(&prepared, Some(main));
        let step = crate::recursive_step::dummy_recursive_step_width2_proof(
            &prepared,
            step_indexes.1.clone(),
        );
        if std::env::var_os("PICKLES_PROFILE").is_some() {
            eprintln!(
                "pickles compile N2: step domain=2^{} rows={}",
                step_indexes.1.index.domain.log_size_of_group,
                step_indexes.0.index.cs.gates.len(),
            );
        }
        let wrap_branches = vec![crate::api::WrapBranchData::from_step_verifier(
            &step_indexes.1.index,
            2,
        )];
        let mut prepared_wrap = crate::recursive_step::prepare_recursive_wrap_width2::<
            RecordedApp,
            16,
            40,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N2_STEP_STMT_LEN,
            RECORDED_N2_STEP_ROUNDS,
            RECORDED_N2_WRAP_STMT_LEN,
        >([first_base, second_base], &step);
        prepared_wrap.data.branches = wrap_branches.clone();
        let wrap_indexes = crate::recursive_step::compile_prepared_recursive_wrap(&prepared_wrap);
        Ok(Self {
            circuit,
            wrap_branches,
            step_indexes: Some(step_indexes),
            wrap_indexes: Some(wrap_indexes),
        })
    }

    /// The historical N2 compile that ran a bootstrap width-2 proof. Kept
    /// as the reference the proof-free `compile` is tested against.
    #[doc(hidden)]
    pub fn compile_with_bootstrap_proofs_reference(
        first: &RecordedProofHandle,
        second: &RecordedProofHandle,
        circuit: RecordedCircuit,
        witness: Vec<Fp>,
    ) -> Result<Self, RecordedProveError> {
        circuit.validate()?;
        if witness.len() != circuit.aux_count as usize {
            return Err(RecordedProveError::Circuit(
                RecordedCircuitError::WrongWitnessLength(witness.len()),
            ));
        }
        crate::common::warm_recursion_caches(true);
        let (RecordedProofInner::R16(first_base), RecordedProofInner::R16(second_base)) =
            (&first.inner, &second.inner)
        else {
            return Err(RecordedProveError::RecursiveBackend(
                crate::recursive_step::DirectRecursiveBackendError::InvalidProof,
            ));
        };
        let app_state = circuit.state(&witness);
        let app = RecordedApp {
            circuit: circuit.clone(),
        };
        let main: crate::recursive_step::EmbeddedAppMain =
            std::sync::Arc::new(move |sys, _previous_app_state| app.main(sys, Some(&witness)));
        let wrap_vk_pts = crate::api::wrap_verification_key_points(&first_base.wrap_verifier);
        let first_prepared = crate::recursive_step::prepare_recursive_step_with_state::<
            RecordedApp,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            40,
            RECORDED_N1_STEP_STMT_LEN,
        >(
            first_base,
            wrap_vk_pts.clone(),
            first.app_state.clone(),
            app_state.clone(),
        );
        let second_prepared = crate::recursive_step::prepare_recursive_step_with_state::<
            RecordedApp,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            40,
            RECORDED_N1_STEP_STMT_LEN,
        >(
            second_base,
            wrap_vk_pts,
            second.app_state.clone(),
            app_state.clone(),
        );
        let prepared = crate::recursive_step::prepare_recursive_step_width2::<
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N2_STEP_STMT_LEN,
        >(first_prepared, second_prepared, app_state);
        let step_indexes = crate::recursive_step::compile_prepared_recursive_step_width2::<
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N2_STEP_STMT_LEN,
        >(&prepared, Some(main.clone()));
        let (step, step_indexes) = crate::recursive_step::prove_prepared_recursive_step_width2(
            prepared,
            Some(main),
            Some(step_indexes),
        );
        if std::env::var_os("PICKLES_PROFILE").is_some() {
            eprintln!(
                "pickles compile N2: step domain=2^{} rows={}",
                step_indexes.1.index.domain.log_size_of_group,
                step_indexes.0.index.cs.gates.len(),
            );
        }
        let wrap_branches = vec![crate::api::WrapBranchData::from_step_verifier(
            &step_indexes.1.index,
            2,
        )];
        let mut prepared_wrap = crate::recursive_step::prepare_recursive_wrap_width2::<
            RecordedApp,
            16,
            40,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N2_STEP_STMT_LEN,
            RECORDED_N2_STEP_ROUNDS,
            RECORDED_N2_WRAP_STMT_LEN,
        >([first_base, second_base], &step);
        prepared_wrap.data.branches = wrap_branches.clone();
        let wrap_indexes = crate::recursive_step::compile_prepared_recursive_wrap(&prepared_wrap);
        Ok(Self {
            circuit,
            wrap_branches,
            step_indexes: Some(step_indexes),
            wrap_indexes: Some(wrap_indexes),
        })
    }

    pub fn prove(
        &mut self,
        first: &RecordedProofHandle,
        second: &RecordedProofHandle,
        witness: Vec<Fp>,
    ) -> Result<RecordedN2Proof, RecordedProveError> {
        crate::common::warm_recursion_caches(true);
        let (RecordedProofInner::R16(first_base), RecordedProofInner::R16(second_base)) =
            (&first.inner, &second.inner)
        else {
            return Err(RecordedProveError::RecursiveBackend(
                crate::recursive_step::DirectRecursiveBackendError::InvalidProof,
            ));
        };
        if witness.len() != self.circuit.aux_count as usize {
            return Err(RecordedProveError::Circuit(
                RecordedCircuitError::WrongWitnessLength(witness.len()),
            ));
        }
        let app_state = self.circuit.state(&witness);
        let app = RecordedApp {
            circuit: self.circuit.clone(),
        };
        let main: crate::recursive_step::EmbeddedAppMain =
            std::sync::Arc::new(move |sys, _previous_app_state| app.main(sys, Some(&witness)));
        let wrap_vk_pts = crate::api::wrap_verification_key_points(&first_base.wrap_verifier);
        let first_prepared = crate::recursive_step::prepare_recursive_step_with_state::<
            RecordedApp,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            40,
            RECORDED_N1_STEP_STMT_LEN,
        >(
            first_base,
            wrap_vk_pts.clone(),
            first.app_state.clone(),
            app_state.clone(),
        );
        let second_prepared = crate::recursive_step::prepare_recursive_step_with_state::<
            RecordedApp,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            40,
            RECORDED_N1_STEP_STMT_LEN,
        >(
            second_base,
            wrap_vk_pts,
            second.app_state.clone(),
            app_state.clone(),
        );
        let accumulators = [
            first_prepared.verified_wrap_accumulator,
            second_prepared.verified_wrap_accumulator,
        ];
        let challenges = [
            first_prepared.finalized_step_challenges.clone(),
            second_prepared.finalized_step_challenges.clone(),
        ];
        let prepared = crate::recursive_step::prepare_recursive_step_width2::<
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N2_STEP_STMT_LEN,
        >(first_prepared, second_prepared, app_state.clone());
        let indexes = self.step_indexes.take().expect("compiled N2 Step indexes");
        let (step, indexes) = crate::recursive_step::prove_prepared_recursive_step_width2(
            prepared,
            Some(main),
            Some(indexes),
        );
        self.step_indexes = Some(indexes);
        let mut prepared_wrap = crate::recursive_step::prepare_recursive_wrap_width2::<
            RecordedApp,
            16,
            40,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N2_STEP_STMT_LEN,
            RECORDED_N2_STEP_ROUNDS,
            RECORDED_N2_WRAP_STMT_LEN,
        >([first_base, second_base], &step);
        prepared_wrap.data.branches = self.wrap_branches.clone();
        let indexes = self.wrap_indexes.take().expect("compiled N2 Wrap indexes");
        let (wrap, indexes) =
            crate::recursive_step::prove_prepared_recursive_wrap(prepared_wrap, Some(indexes));
        self.wrap_indexes = Some(indexes);
        let encoded = wrap
            .to_mina_network_proof(step.verifier.index.domain.log_size_of_group as u8)
            .map_err(RecordedProveError::RecursiveBackend)?;
        Ok(RecordedN2Proof {
            app_state,
            proof: encoded,
            challenge_polynomial_commitments: accumulators,
            old_bulletproof_challenges: challenges,
            dlog_plonk_index: step.messages_for_next_step_vk_pts,
        })
    }
}

#[derive(Clone)]
struct RecordedProgramTemplateApp;

impl StepApp for RecordedProgramTemplateApp {
    type Witness = ();

    fn main(
        &self,
        _sys: &mut RunState<Fp>,
        _witness: Option<&Self::Witness>,
    ) -> SnarkyResult<Vec<FieldVar<Fp>>> {
        Ok(vec![FieldVar::constant(Fp::from(0u64))])
    }

    fn state(&self, _witness: &Self::Witness) -> Vec<Fp> {
        vec![Fp::from(0u64)]
    }
}

#[derive(Clone)]
pub struct RecordedProgramBranch {
    pub circuit: RecordedCircuit,
    pub witness: Vec<Fp>,
    pub proofs_verified: u8,
}

type RecordedProgramStepIndexesShaped<const STEP_PI: usize, const ACTIVE: usize> =
    crate::recursive_step::RecursiveStepWidth2Indexes<
        RECORDED_N1_STEP_ROUNDS,
        RECORDED_BASE_WRAP_ROUNDS,
        RECORDED_N1_STEP_STMT_LEN,
        STEP_PI,
        ACTIVE,
    >;
fn compile_recorded_program_steps<const STEP_PI: usize, const ACTIVE: usize>(
    branches: &[RecordedProgramBranch],
    template: &crate::api::BaseCaseProof<RecordedProgramTemplateApp, 16, 40>,
    wrap_vk: &[(Fp, Fp)],
    wrap_index: &kimchi::verifier_index::VerifierIndex<
        { snarky::FULL_ROUNDS },
        Pallas,
        poly_commitment::ipa::SRS<Pallas>,
    >,
    finalize_index: Option<
        &kimchi::verifier_index::VerifierIndex<
            { snarky::FULL_ROUNDS },
            Vesta,
            poly_commitment::ipa::SRS<Vesta>,
        >,
    >,
    finalize_domain_log2s: &[u32],
) -> Vec<Option<RecordedProgramStepIndexesShaped<STEP_PI, ACTIVE>>> {
    branches
        .iter()
        .map(|branch| {
            Some(compile_recorded_program_step_branch::<STEP_PI, ACTIVE>(
                branch,
                template,
                wrap_vk,
                wrap_index,
                finalize_index,
                finalize_domain_log2s,
            ))
        })
        .collect()
}

/// Compiles the step indexes of every branch in one pass: the first N0
/// branch first (its index is the program's shared finalize index; aligning
/// it to itself is a no-op), then every other branch — sequentially — aligned
/// to it (each branch already parallelizes internally over the pool).
fn compile_recorded_program_steps_single_pass<const STEP_PI: usize, const ACTIVE: usize>(
    branches: &[RecordedProgramBranch],
    template: &crate::api::BaseCaseProof<RecordedProgramTemplateApp, 16, 40>,
    wrap_vk: &[(Fp, Fp)],
    wrap_index: &kimchi::verifier_index::VerifierIndex<
        { snarky::FULL_ROUNDS },
        Pallas,
        poly_commitment::ipa::SRS<Pallas>,
    >,
    finalize_domain_log2s: &[u32],
) -> Vec<Option<RecordedProgramStepIndexesShaped<STEP_PI, ACTIVE>>> {
    use rayon::prelude::*;
    let first_n0 = branches.iter().position(|b| b.proofs_verified == 0);
    let n0_indexes = first_n0.map(|i| {
        compile_recorded_program_step_branch::<STEP_PI, ACTIVE>(
            &branches[i],
            template,
            wrap_vk,
            wrap_index,
            None,
            finalize_domain_log2s,
        )
    });
    let finalize_index = n0_indexes.as_ref().map(|indexes| &indexes.1.index);
    let rest: Vec<usize> = (0..branches.len())
        .filter(|&i| Some(i) != first_n0)
        .collect();
    // Sequential: each branch's step compile already parallelizes internally
    // over the rayon pool, so iterating branches in parallel too nests
    // parallelism on a bounded pool and deadlocks under contention.
    let compiled: Vec<(usize, RecordedProgramStepIndexesShaped<STEP_PI, ACTIVE>)> = rest
        .into_iter()
        .map(|i| {
            (
                i,
                compile_recorded_program_step_branch::<STEP_PI, ACTIVE>(
                    &branches[i],
                    template,
                    wrap_vk,
                    wrap_index,
                    finalize_index,
                    finalize_domain_log2s,
                ),
            )
        })
        .collect();
    let mut out: Vec<Option<RecordedProgramStepIndexesShaped<STEP_PI, ACTIVE>>> =
        (0..branches.len()).map(|_| None).collect();
    for (i, indexes) in compiled {
        out[i] = Some(indexes);
    }
    if let (Some(i), Some(indexes)) = (first_n0, n0_indexes) {
        out[i] = Some(indexes);
    }
    out
}

/// OCaml `Fix_domains.rough_domains` (2^20): the placeholder finalize
/// domain list every branch is synthesized with when *probing* its own
/// natural domain, before the real per-branch list exists.
const FIX_DOMAINS_ROUGH_LOG2: u32 = 20;

type StepFinalizeIndex = kimchi::verifier_index::VerifierIndex<
    { snarky::FULL_ROUNDS },
    Vesta,
    poly_commitment::ipa::SRS<Vesta>,
>;

/// The shared prepared-step construction of the program step compiles and
/// the domain probe, generic over the program width (`STEP_PI` = the step
/// statement length, `ACTIVE` = the arity: <67, 2> or <34, 1>).
fn build_recorded_program_step_prepared<const STEP_PI: usize, const ACTIVE: usize>(
    branch: &RecordedProgramBranch,
    template: &crate::api::BaseCaseProof<RecordedProgramTemplateApp, 16, 40>,
    wrap_vk: &[(Fp, Fp)],
    wrap_index: &kimchi::verifier_index::VerifierIndex<
        { snarky::FULL_ROUNDS },
        Pallas,
        poly_commitment::ipa::SRS<Pallas>,
    >,
    finalize_index: Option<&StepFinalizeIndex>,
    finalize_domain_log2s: &[u32],
) -> (
    crate::recursive_step::PreparedRecursiveStepWidth2<
        RECORDED_N1_STEP_STMT_LEN,
        STEP_PI,
    >,
    crate::recursive_step::EmbeddedAppMain,
) {
    let branch = branch.clone();
    let app_state = branch.circuit.state(&branch.witness);
    let prepared = crate::recursive_step::prepare_recursive_step_with_state::<
        RecordedProgramTemplateApp,
        16,
        RECORDED_BASE_WRAP_ROUNDS,
        40,
        RECORDED_N1_STEP_STMT_LEN,
    >(
        template,
        wrap_vk.to_vec(),
        vec![Fp::from(0u64); app_state.len()],
        app_state.clone(),
    );
    let prepared = crate::recursive_step::normalize_program_recursive_step(prepared);
    let prepared = crate::recursive_step::align_program_recursive_step_verifier::<
        RECORDED_N1_STEP_ROUNDS,
        RECORDED_N1_STEP_STMT_LEN,
    >(prepared, wrap_index);
    let prepared = match finalize_index {
        Some(index) => {
            crate::recursive_step::align_program_recursive_step_finalize_index(prepared, index)
        }
        None => prepared,
    };
    let prepared = crate::recursive_step::align_program_recursive_step_finalize_domains(
        prepared,
        finalize_domain_log2s,
    );
    let prepared = match branch.proofs_verified {
        0 => crate::recursive_step::prepare_recursive_step_n0::<
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            STEP_PI,
        >(prepared, app_state),
        1 => crate::recursive_step::prepare_recursive_step_n1::<
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            STEP_PI,
        >(prepared, app_state),
        2 => {
            assert_eq!(ACTIVE, 2, "a width-1 program cannot hold a pv=2 branch");
            crate::recursive_step::prepare_recursive_step_width2::<
                RECORDED_BASE_WRAP_ROUNDS,
                RECORDED_N1_STEP_STMT_LEN,
                STEP_PI,
            >(prepared.clone(), prepared, app_state)
        }
        _ => unreachable!(),
    };
    let prepared = apply_previous_proof_widths(prepared, &branch, ACTIVE);
    let app = RecordedApp {
        circuit: branch.circuit.clone(),
    };
    let witness = branch.witness.clone();
    let main: crate::recursive_step::EmbeddedAppMain =
        std::sync::Arc::new(move |sys, previous_app_state| {
            app.main_with_previous_app_state(sys, Some(&witness), previous_app_state)
        });
    (prepared, main)
}

/// Stamps each REAL slot's `local_max_proofs_verified` (the verified
/// proof's own width, from the recording) onto the prepared step's per-proof
/// data. Logical previous `i` sits at physical slot `active - pv + i`
/// (front-padded).
fn apply_previous_proof_widths<const W1: usize, const PI: usize>(
    mut prepared: crate::recursive_step::PreparedRecursiveStepWidth2<W1, PI>,
    branch: &RecordedProgramBranch,
    active: usize,
) -> crate::recursive_step::PreparedRecursiveStepWidth2<W1, PI> {
    let pv = branch.proofs_verified as usize;
    let widths = &branch.circuit.previous_proof_widths;
    if !widths.is_empty() {
        assert_eq!(widths.len(), pv, "one recorded width per verified proof");
        for (i, &width) in widths.iter().enumerate() {
            let slot = active - pv + i;
            prepared.proofs[slot].local_max_proofs_verified = Some(width as usize);
        }
    }
    for constraint in &branch.circuit.constraints {
        if let RecordedConstraint::SideLoadedVk { proof, .. } = constraint {
            let slot = active - pv + *proof as usize;
            prepared.proofs[slot].side_loaded_lagranges =
                Some(side_loaded_x_hat_lagranges().clone());
        }
    }
    prepared
}

/// The per-element `(lagrange, correction)` constants of the three
/// selectable side-loaded wrap domains (2^13/14/15 over the shared Tock
/// SRS), in one-hot order, transposed per statement element.
fn side_loaded_x_hat_lagranges() -> &'static Vec<Vec<((Fp, Fp), (Fp, Fp))>> {
    static CACHE: std::sync::OnceLock<Vec<Vec<((Fp, Fp), (Fp, Fp))>>> = std::sync::OnceLock::new();
    CACHE.get_or_init(|| {
        use ark_poly::EvaluationDomain as _;
        use poly_commitment::SRS as _;
        let srs = crate::common::tock_srs(1 << crate::common::TOCK_ROUNDS);
        let per_domain: Vec<Vec<((Fp, Fp), (Fp, Fp))>> = (13..=15u32)
            .map(|log2| {
                let domain =
                    ark_poly::Radix2EvaluationDomain::<mina_curves::pasta::Fq>::new(1 << log2)
                        .expect("wrap domain");
                let basis = srs.get_lagrange_basis(domain);
                crate::recursive_step::wrap_x_hat_lagranges(&basis, RECORDED_N1_STEP_ROUNDS).0
            })
            .collect();
        (0..per_domain[0].len())
            .map(|element| per_domain.iter().map(|domain| domain[element]).collect())
            .collect()
    })
}

/// Debug-only: the probe's prepared step WITHOUT the Selected domain list
/// (historical fixed-finalize path).
fn build_recorded_program_step_prepared_fixed_for_debug<const STEP_PI: usize, const ACTIVE: usize>(
    branch: &RecordedProgramBranch,
    template: &crate::api::BaseCaseProof<RecordedProgramTemplateApp, 16, 40>,
    wrap_vk: &[(Fp, Fp)],
    wrap_index: &kimchi::verifier_index::VerifierIndex<
        { snarky::FULL_ROUNDS },
        Pallas,
        poly_commitment::ipa::SRS<Pallas>,
    >,
    skip_verifier_align: bool,
) -> (
    crate::recursive_step::PreparedRecursiveStepWidth2<
        RECORDED_N1_STEP_STMT_LEN,
        RECORDED_N2_STEP_STMT_LEN,
    >,
    crate::recursive_step::EmbeddedAppMain,
) {
    let branch = branch.clone();
    let app_state = branch.circuit.state(&branch.witness);
    let prepared = crate::recursive_step::prepare_recursive_step_with_state::<
        RecordedProgramTemplateApp,
        16,
        RECORDED_BASE_WRAP_ROUNDS,
        40,
        RECORDED_N1_STEP_STMT_LEN,
    >(
        template,
        wrap_vk.to_vec(),
        vec![Fp::from(0u64); app_state.len()],
        app_state.clone(),
    );
    let prepared = crate::recursive_step::normalize_program_recursive_step(prepared);
    let prepared = if skip_verifier_align {
        prepared
    } else {
        crate::recursive_step::align_program_recursive_step_verifier::<
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
        >(prepared, wrap_index)
    };
    let prepared = match branch.proofs_verified {
        0 => crate::recursive_step::prepare_recursive_step_n0::<
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N2_STEP_STMT_LEN,
        >(prepared, app_state),
        1 => crate::recursive_step::prepare_recursive_step_n1::<
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N2_STEP_STMT_LEN,
        >(prepared, app_state),
        2 => crate::recursive_step::prepare_recursive_step_width2::<
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N2_STEP_STMT_LEN,
        >(prepared.clone(), prepared, app_state),
        _ => unreachable!(),
    };
    let app = RecordedApp {
        circuit: branch.circuit.clone(),
    };
    let witness = branch.witness.clone();
    let main: crate::recursive_step::EmbeddedAppMain =
        std::sync::Arc::new(move |sys, previous_app_state| {
            app.main_with_previous_app_state(sys, Some(&witness), previous_app_state)
        });
    (prepared, main)
}

fn compile_recorded_program_step_branch<const STEP_PI: usize, const ACTIVE: usize>(
    branch: &RecordedProgramBranch,
    template: &crate::api::BaseCaseProof<RecordedProgramTemplateApp, 16, 40>,
    wrap_vk: &[(Fp, Fp)],
    wrap_index: &kimchi::verifier_index::VerifierIndex<
        { snarky::FULL_ROUNDS },
        Pallas,
        poly_commitment::ipa::SRS<Pallas>,
    >,
    finalize_index: Option<&StepFinalizeIndex>,
    finalize_domain_log2s: &[u32],
) -> RecordedProgramStepIndexesShaped<STEP_PI, ACTIVE> {
    let (prepared, main) = build_recorded_program_step_prepared::<STEP_PI, ACTIVE>(
        branch,
        template,
        wrap_vk,
        wrap_index,
        finalize_index,
        finalize_domain_log2s,
    );
    crate::recursive_step::compile_prepared_recursive_step_width2_arity::<
        RECORDED_N1_STEP_ROUNDS,
        RECORDED_BASE_WRAP_ROUNDS,
        RECORDED_N1_STEP_STMT_LEN,
        STEP_PI,
        ACTIVE,
    >(&prepared, Some(main))
}

/// OCaml `Fix_domains.domains`: synthesizes the branch's step constraint
/// system with the rough placeholder domain list and returns its natural
/// domain. No SRS or commitment work happens here.
fn recorded_program_step_branch_domain_log2<const STEP_PI: usize, const ACTIVE: usize>(
    branch: &RecordedProgramBranch,
    template: &crate::api::BaseCaseProof<RecordedProgramTemplateApp, 16, 40>,
    wrap_vk: &[(Fp, Fp)],
    wrap_index: &kimchi::verifier_index::VerifierIndex<
        { snarky::FULL_ROUNDS },
        Pallas,
        poly_commitment::ipa::SRS<Pallas>,
    >,
) -> u32 {
    let t0 = snarky::wasm_instant::Instant::now();
    let (prepared, main) = build_recorded_program_step_prepared::<STEP_PI, ACTIVE>(
        branch,
        template,
        wrap_vk,
        wrap_index,
        None,
        &[FIX_DOMAINS_ROUGH_LOG2],
    );
    let t1 = snarky::wasm_instant::Instant::now();
    let log2 = crate::recursive_step::domain_log2_prepared_recursive_step_width2_arity::<
        RECORDED_N1_STEP_ROUNDS,
        RECORDED_BASE_WRAP_ROUNDS,
        RECORDED_N1_STEP_STMT_LEN,
        STEP_PI,
        ACTIVE,
    >(&prepared, Some(main));
    crate::recorded::record_probe_timing(format!(
        "pv{} prepare {:.2?} + synth/cs {:.2?} -> 2^{log2}",
        branch.proofs_verified,
        t1 - t0,
        t1.elapsed()
    ));
    log2
}

/// Debug: isolates the probe's sub-steps for one branch. `mode`:
/// 0 = prepared only; 1 = prepared + domain probe with the FIXED finalize
/// (empty domain list); 2 = prepared + domain probe with the rough SELECTED
/// list (the real probe). Returns a timing report.
#[doc(hidden)]
pub fn debug_probe_branch(
    branches: Vec<RecordedProgramBranch>,
    branch_index: usize,
    mode: u32,
) -> Result<String, RecordedProveError> {
    let template_compiled = crate::api::CompiledBaseCase::<RecordedProgramTemplateApp, 16, 40>::compile(
        RecordedProgramTemplateApp,
        (),
    );
    let mut template_compiled = template_compiled;
    let template = template_compiled.prove(());
    let bootstrap_vk = crate::api::wrap_verification_key_points(&template.wrap_verifier);
    let branch = branches
        .get(branch_index)
        .ok_or_else(|| RecordedProveError::Program("unknown branch".into()))?;
    let t0 = snarky::wasm_instant::Instant::now();
    let (prepared, main) = if mode == 1 || mode == 3 {
        // FIXED finalize: bypass the domain-list align entirely; mode 3
        // additionally skips the verifier align (share_index_sponge).
        build_recorded_program_step_prepared_fixed_for_debug::<RECORDED_N2_STEP_STMT_LEN, 2>(
            branch,
            &template,
            &bootstrap_vk,
            &template.wrap_verifier.index,
            mode == 3,
        )
    } else {
        build_recorded_program_step_prepared::<RECORDED_N2_STEP_STMT_LEN, 2>(
            branch,
            &template,
            &bootstrap_vk,
            &template.wrap_verifier.index,
            None,
            &[FIX_DOMAINS_ROUGH_LOG2],
        )
    };
    let prepare_elapsed = t0.elapsed();
    if mode == 0 {
        return Ok(format!("prepared only: {prepare_elapsed:.2?}"));
    }
    let t1 = snarky::wasm_instant::Instant::now();
    let probed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        crate::recursive_step::domain_log2_prepared_recursive_step_width2::<
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N2_STEP_STMT_LEN,
        >(&prepared, Some(main))
    }));
    match probed {
        Ok(log2) => Ok(format!(
            "mode {mode}: prepared {prepare_elapsed:.2?}, probe {:.2?} -> 2^{log2}",
            t1.elapsed()
        )),
        Err(payload) => {
            let message = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_string()))
                .unwrap_or_else(|| "non-string panic payload".to_string());
            Ok(format!(
                "mode {mode}: prepared {prepare_elapsed:.2?}, probe PANICKED after {:.2?}: {message}",
                t1.elapsed()
            ))
        }
    }
}

/// Live trace hook (wasm: console.log via kimchi-wasm) — lets the host see
/// checkpoints from pool workers in real time, since wasm has no stderr and
/// a hung pool never returns.
static TRACE_HOOK: std::sync::Mutex<Option<fn(&str)>> = std::sync::Mutex::new(None);

pub fn set_trace_hook(hook: fn(&str)) {
    *TRACE_HOOK.lock().unwrap() = Some(hook);
}

pub(crate) fn trace(message: &str) {
    if let Ok(hook) = TRACE_HOOK.lock() {
        if let Some(hook) = *hook {
            hook(message);
        }
    }
}

/// Probe sub-step timings, readable through the debug-stage report (wasm has
/// no stderr).
static PROBE_TIMINGS: std::sync::Mutex<Vec<String>> = std::sync::Mutex::new(Vec::new());

pub(crate) fn record_probe_timing(entry: String) {
    if let Ok(mut timings) = PROBE_TIMINGS.lock() {
        timings.push(entry);
    }
}

fn take_probe_timings() -> Vec<String> {
    PROBE_TIMINGS
        .lock()
        .map(|mut timings| std::mem::take(&mut *timings))
        .unwrap_or_default()
}

/// Per-slot `local_max_proofs_verified`: for each of the program's `active`
/// physical slots, the max over branches of the width of the proof verified
/// in that slot (front-padded alignment). Legacy recordings (no widths)
/// default every slot to the program width.
fn recorded_slot_local_max(branches: &[RecordedProgramBranch], active: usize) -> Vec<usize> {
    (0..active)
        .map(|j| {
            branches
                .iter()
                .filter_map(|branch| {
                    let pv = branch.proofs_verified as usize;
                    let front_pad = active - pv;
                    if j < front_pad {
                        return None;
                    }
                    let i = j - front_pad;
                    Some(if branch.circuit.previous_proof_widths.is_empty() {
                        active
                    } else {
                        branch.circuit.previous_proof_widths[i] as usize
                    })
                })
                .max()
                .unwrap_or(active)
        })
        .collect()
}

const RECORDED_PROGRAM_CACHE_VERSION: u32 = 1;

#[derive(serde::Serialize, serde::Deserialize)]
struct RecordedProgramIndexCache {
    version: u32,
    branches_digest: [u8; 32],
    /// Per-branch step VERIFIER indexes (rmp) — the prover indexes are
    /// rebuilt lazily from the re-synthesized circuits.
    step_verifiers: Vec<Vec<u8>>,
    /// The shared wrap VERIFIER index (rmp).
    wrap_verifier: Vec<u8>,
}

type RecordedRawStepVerifier = kimchi::verifier_index::VerifierIndex<
    { snarky::FULL_ROUNDS },
    Vesta,
    poly_commitment::ipa::SRS<Vesta>,
>;
type RecordedRawWrapVerifier = kimchi::verifier_index::VerifierIndex<
    { snarky::FULL_ROUNDS },
    Pallas,
    poly_commitment::ipa::SRS<Pallas>,
>;

fn restore_step_verifier(mut vi: RecordedRawStepVerifier) -> RecordedRawStepVerifier {
    crate::template_dummy::fixup_vi(&mut vi, crate::common::tick_srs(1 << crate::common::TICK_ROUNDS));
    vi
}

fn restore_wrap_verifier(mut vi: RecordedRawWrapVerifier) -> RecordedRawWrapVerifier {
    crate::template_dummy::fixup_vi(&mut vi, crate::common::tock_srs(1 << crate::common::TOCK_ROUNDS));
    vi
}

fn recorded_program_branches_digest(branches: &[RecordedProgramBranch]) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    for branch in branches {
        hasher.update([branch.proofs_verified]);
        hasher.update(serde_json::to_vec(&branch.circuit).expect("circuit serializes"));
    }
    hasher.finalize().into()
}

fn recorded_program_wrap_branches<const STEP_PI: usize, const ACTIVE: usize>(
    branches: &[RecordedProgramBranch],
    indexes: &[Option<RecordedProgramStepIndexesShaped<STEP_PI, ACTIVE>>],
) -> Vec<crate::api::WrapBranchData> {
    branches
        .iter()
        .zip(indexes)
        .map(|(branch, indexes)| {
            crate::api::WrapBranchData::from_step_verifier(
                &indexes.as_ref().unwrap().1.index,
                branch.proofs_verified as usize,
            )
        })
        .collect()
}

type RecordedTemplateBase = crate::api::BaseCaseProof<RecordedProgramTemplateApp, 16, 40>;
type RecordedBootstrapStepShaped<const STEP_PI: usize, const ACTIVE: usize> =
    crate::recursive_step::RecursiveStepWidth2Proof<
        RECORDED_N1_STEP_ROUNDS,
        RECORDED_BASE_WRAP_ROUNDS,
        RECORDED_N1_STEP_STMT_LEN,
        STEP_PI,
        ACTIVE,
    >;
type RecordedBootstrapStep = RecordedBootstrapStepShaped<RECORDED_N2_STEP_STMT_LEN, 2>;

/// Live prove of the bootstrap step at one program shape: an N0 recursive
/// step over the template base cycle, whose index structure seeds every
/// placeholder branch of that shape.
fn manufacture_bootstrap_step<const STEP_PI: usize, const ACTIVE: usize>(
    template: &RecordedTemplateBase,
) -> RecordedBootstrapStepShaped<STEP_PI, ACTIVE> {
    let bootstrap_vk = crate::api::wrap_verification_key_points(&template.wrap_verifier);
    let bootstrap = crate::recursive_step::prepare_recursive_step_with_state::<
        RecordedProgramTemplateApp,
        16,
        RECORDED_BASE_WRAP_ROUNDS,
        40,
        RECORDED_N1_STEP_STMT_LEN,
    >(
        template,
        bootstrap_vk,
        vec![Fp::from(0u64)],
        vec![Fp::from(0u64)],
    );
    let bootstrap = crate::recursive_step::normalize_program_recursive_step(bootstrap);
    let bootstrap = crate::recursive_step::prepare_recursive_step_n0::<
        RECORDED_BASE_WRAP_ROUNDS,
        RECORDED_N1_STEP_STMT_LEN,
        STEP_PI,
    >(bootstrap, vec![Fp::from(0u64)]);
    crate::recursive_step::prove_prepared_recursive_step_width2_arity::<
        RECORDED_N1_STEP_ROUNDS,
        RECORDED_BASE_WRAP_ROUNDS,
        RECORDED_N1_STEP_STMT_LEN,
        STEP_PI,
        ACTIVE,
    >(bootstrap, None, None)
    .0
}

/// Live manufacture of the compile-time dummies: the template base cycle
/// proof and the bootstrap width-2 step proof. This is what
/// [`crate::template_dummy`] embeds; the program compile only runs it when
/// the embedded blob is absent or stale.
fn manufacture_template_dummies() -> (RecordedTemplateBase, RecordedBootstrapStep) {
    let mut template_compiled = crate::api::CompiledBaseCase::<RecordedProgramTemplateApp, 16, 40>::compile(
        RecordedProgramTemplateApp,
        (),
    );
    let template = template_compiled.prove(());
    let bootstrap_step = manufacture_bootstrap_step::<RECORDED_N2_STEP_STMT_LEN, 2>(&template);
    (template, bootstrap_step)
}

/// Shape-directed acquisition of the compile-time dummies. The embedded blob
/// carries the width-2 bootstrap; the width-1 shape reuses the embedded
/// template and proves its own bootstrap live (blob extension to follow).
trait ProgramTemplateDummies: Sized {
    fn template_dummies() -> (RecordedTemplateBase, Self);
}

impl ProgramTemplateDummies for RecordedBootstrapStepShaped<RECORDED_N2_STEP_STMT_LEN, 2> {
    fn template_dummies() -> (RecordedTemplateBase, Self) {
        match crate::template_dummy::decode_embedded().and_then(assemble_template_dummies) {
            Some(pair) => pair,
            None => manufacture_template_dummies(),
        }
    }
}

impl ProgramTemplateDummies for RecordedBootstrapStepShaped<RECORDED_N1_STEP_STMT_LEN, 1> {
    fn template_dummies() -> (RecordedTemplateBase, Self) {
        let template = match crate::template_dummy::decode_embedded()
            .and_then(assemble_template_dummies)
        {
            Some((template, _)) => template,
            None => manufacture_template_dummies().0,
        };
        let bootstrap_step =
            manufacture_bootstrap_step::<RECORDED_N1_STEP_STMT_LEN, 1>(&template);
        (template, bootstrap_step)
    }
}

/// Rebuilds the typed template/bootstrap artifacts from decoded blob parts.
/// `None` on any shape mismatch (→ live fallback).
fn assemble_template_dummies(
    parts: crate::template_dummy::DummyParts,
) -> Option<(RecordedTemplateBase, RecordedBootstrapStep)> {
    let template = crate::api::BaseCaseProof {
        statement: parts.template_statement,
        stable_statement: parts.template_stable,
        proof: parts.template_proof,
        step_proof: parts.template_step_proof,
        step_verifier: snarky::api::VerifierIndexWrapper {
            index: parts.template_step_vi,
        },
        wrap_verifier: snarky::api::VerifierIndexWrapper {
            index: parts.template_wrap_vi,
        },
        wrap_vk_pts: parts.template_wrap_vk_pts,
    };
    let statement: [Fp; RECORDED_N2_STEP_STMT_LEN] = parts.boot_statement.try_into().ok()?;
    let bootstrap = crate::recursive_step::RecursiveStepWidth2Proof {
        statement,
        proof: parts.boot_proof,
        verifier: snarky::api::VerifierIndexWrapper {
            index: parts.boot_vi,
        },
        messages_for_next_step_vk_pts: parts.boot_vk_pts,
        messages_for_next_step_proof: parts.boot_m4n,
    };
    Some((template, bootstrap))
}

/// A synthetic structure-donor wrap verifier index. The steps consume only
/// STRUCTURAL data from the donor: its domain (which fixes the x_hat
/// Lagrange commitment constants through the shared Tock SRS), its shifts,
/// and 28 commitment slots whose point VALUES are witness data in the step
/// circuits. A full donor wrap prover compile is therefore unnecessary —
/// this mirrors `verify::wrap_verifier_index_from_side_loaded` with
/// placeholder points, and OCaml's static `Wrap_domains` table, which never
/// compiles a donor either.
fn synthetic_structure_wrap_index(
    wrap_domain_log2: u32,
) -> snarky::api::VerifierIndexWrapper<
    crate::api::WrapCircuit<RECORDED_N2_STEP_ROUNDS, RECORDED_N2_WRAP_STMT_LEN>,
> {
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_poly::EvaluationDomain as _;
    use kimchi::circuits::polynomials::permutation::{
        permutation_vanishing_polynomial, zk_w, Shifts,
    };
    use kimchi::curve::KimchiCurve as _;
    use kimchi::linearization::expr_linearization;
    use poly_commitment::commitment::PolyComm;
    use poly_commitment::SRS as _;

    let domain = ark_poly::Radix2EvaluationDomain::<mina_curves::pasta::Fq>::new(
        1usize << wrap_domain_log2,
    )
    .expect("wrap domain size is a supported power of two");
    let srs = crate::common::tock_srs(1 << crate::common::TOCK_ROUNDS);
    srs.get_lagrange_basis(domain);

    let generator = Pallas::generator().into_group();
    let comm = |i: u64| PolyComm {
        chunks: vec![(generator * mina_curves::pasta::Fq::from(i + 1)).into_affine()],
    };

    let feature_flags = kimchi::circuits::constraints::FeatureFlags {
        range_check0: false,
        range_check1: false,
        foreign_field_add: false,
        foreign_field_mul: false,
        xor: false,
        rot: false,
        lookup_features: kimchi::circuits::lookup::lookups::LookupFeatures {
            patterns: kimchi::circuits::lookup::lookups::LookupPatterns {
                xor: false,
                lookup: false,
                range_check: false,
                foreign_field_mul: false,
            },
            joint_lookup_used: false,
            uses_runtime_tables: false,
        },
    };
    let (linearization, powers_of_alpha) = expr_linearization(Some(&feature_flags), true);
    let zk_rows = kimchi::circuits::constraints::ZK_ROWS_BY_DEFAULT;
    let shifts = Shifts::new(&domain);
    let index = kimchi::verifier_index::VerifierIndex {
        domain,
        max_poly_size: srs.max_poly_size(),
        zk_rows,
        srs,
        public: RECORDED_N2_WRAP_STMT_LEN,
        prev_challenges: crate::common::MAX_PROOFS_VERIFIED,
        sigma_comm: core::array::from_fn(|i| comm(i as u64)),
        coefficients_comm: core::array::from_fn(|i| comm(7 + i as u64)),
        generic_comm: comm(22),
        psm_comm: comm(23),
        complete_add_comm: comm(24),
        mul_comm: comm(25),
        emul_comm: comm(26),
        endomul_scalar_comm: comm(27),
        range_check0_comm: None,
        range_check1_comm: None,
        foreign_field_add_comm: None,
        foreign_field_mul_comm: None,
        xor_comm: None,
        rot_comm: None,
        shift: *shifts.shifts(),
        permutation_vanishing_polynomial_m: {
            let cell = std::sync::OnceLock::new();
            cell.set(permutation_vanishing_polynomial(domain, zk_rows))
                .unwrap_or_else(|_| unreachable!("fresh OnceLock"));
            cell
        },
        w: {
            let cell = std::sync::OnceLock::new();
            cell.set(zk_w(domain, zk_rows))
                .unwrap_or_else(|_| unreachable!("fresh OnceLock"));
            cell
        },
        endo: *Pallas::other_curve_endo(),
        lookup_index: None,
        linearization,
        powers_of_alpha,
    };
    snarky::api::VerifierIndexWrapper { index }
}

/// Runs the live dummy manufacture and encodes the blob bytes — the
/// regeneration entrypoint (`generate_template_dummy_blob` test).
pub fn template_dummy_blob_bytes() -> Vec<u8> {
    let (template, bootstrap_step) = manufacture_template_dummies();
    let parts = crate::template_dummy::DummyParts {
        template_statement: template.statement,
        template_stable: template.stable_statement,
        template_proof: template.proof,
        template_step_proof: template.step_proof,
        template_step_vi: template.step_verifier.index,
        template_wrap_vi: template.wrap_verifier.index,
        template_wrap_vk_pts: template.wrap_vk_pts,
        boot_statement: bootstrap_step.statement.to_vec(),
        boot_proof: bootstrap_step.proof,
        boot_vi: bootstrap_step.verifier.index,
        boot_vk_pts: bootstrap_step.messages_for_next_step_vk_pts,
        boot_m4n: bootstrap_step.messages_for_next_step_proof,
    };
    crate::template_dummy::encode(&parts)
}

type TemplateVestaSponge = mina_poseidon::sponge::DefaultFqSponge<
    mina_curves::pasta::VestaParameters,
    mina_poseidon::constants::PlonkSpongeConstantsKimchi,
    { snarky::FULL_ROUNDS },
>;
type TemplatePallasSponge = mina_poseidon::sponge::DefaultFqSponge<
    mina_curves::pasta::PallasParameters,
    mina_poseidon::constants::PlonkSpongeConstantsKimchi,
    { snarky::FULL_ROUNDS },
>;

/// Digest freshness probe for the guard test: the step and wrap verifier
/// digests of a LIVE template base compile (no proving).
pub fn template_live_digests() -> (mina_curves::pasta::Fq, Fp) {
    let template_compiled = crate::api::CompiledBaseCase::<RecordedProgramTemplateApp, 16, 40>::compile(
        RecordedProgramTemplateApp,
        (),
    );
    let step_vi = &template_compiled.step_indexes.as_ref().expect("compiled").1;
    let wrap_vi = &template_compiled.wrap_indexes.as_ref().expect("compiled").1;
    (
        step_vi.index.digest::<TemplateVestaSponge>(),
        wrap_vi.index.digest::<TemplatePallasSponge>(),
    )
}

/// The step and wrap verifier digests carried by the embedded blob, when
/// present.
pub fn template_blob_digests() -> Option<(mina_curves::pasta::Fq, Fp)> {
    let parts = crate::template_dummy::decode_embedded()?;
    Some((
        parts.template_step_vi.digest::<TemplateVestaSponge>(),
        parts.template_wrap_vi.digest::<TemplatePallasSponge>(),
    ))
}

/// A recorded Pickles program compiled at one physical width. Every method
/// owns its Step index, while every arity uses one shared maximal Wrap index
/// and verification key.
///
/// `STEP_PI` is the step public-input length and `ACTIVE` the physical proof
/// width (`ACTIVE = (STEP_PI - 1) / (18 + WRAP_ROUNDS)`); the two supported
/// shapes are `<RECORDED_N2_STEP_STMT_LEN, 2>` (width-2 programs) and
/// `<RECORDED_N1_STEP_STMT_LEN, 1>` (width-1 programs, OCaml compiles a
/// program whose branches all have `proofs_verified <= 1` at width 1).
pub struct RecordedCompiledProgramShaped<const STEP_PI: usize, const ACTIVE: usize> {
    branches: Vec<RecordedProgramBranch>,
    wrap_branches: Vec<crate::api::WrapBranchData>,
    /// Per-branch x_hat Lagrange constants of the shared wrap — must be
    /// injected into every prove's wrap witness data so synthesis matches
    /// the compiled (possibly branch-selecting) circuit.
    wrap_statement_lagranges: Vec<
        Vec<(
            (mina_curves::pasta::Fq, mina_curves::pasta::Fq),
            (mina_curves::pasta::Fq, mina_curves::pasta::Fq),
        )>,
    >,
    /// The unique per-branch step-domain list the steps' finalize one-hot
    /// selects over — must be re-injected into every prove-time prepared
    /// step.
    finalize_domain_log2s: Vec<u32>,
    step_indexes: Vec<Option<RecordedProgramStepIndexesShaped<STEP_PI, ACTIVE>>>,
    wrap_indexes: Option<
        crate::recursive_step::RecursiveWrapIndexes<
            RECORDED_N2_STEP_ROUNDS,
            RECORDED_N2_WRAP_STMT_LEN,
        >,
    >,
    template: crate::api::BaseCaseProof<RecordedProgramTemplateApp, 16, 40>,
}

/// The public program handle: one compiled program at either supported
/// physical width. All prove/verify entry points dispatch on the shape.
pub enum RecordedCompiledProgram {
    W2(RecordedCompiledProgramShaped<RECORDED_N2_STEP_STMT_LEN, 2>),
    W1(RecordedCompiledProgramShaped<RECORDED_N1_STEP_STMT_LEN, 1>),
}

macro_rules! with_program_shape {
    ($self:expr, $p:ident => $body:expr) => {
        match $self {
            RecordedCompiledProgram::W2($p) => $body,
            RecordedCompiledProgram::W1($p) => $body,
        }
    };
}

impl RecordedCompiledProgram {
    /// The physical width OCaml `Pickles.compile` gives a program: the max
    /// `proofs_verified` over its branches, floored at 1 (a proof-free
    /// program still compiles at width 1).
    fn shape_width(branches: &[RecordedProgramBranch]) -> usize {
        branches
            .iter()
            .map(|branch| usize::from(branch.proofs_verified))
            .max()
            .unwrap_or(0)
            .max(1)
    }

    /// Compiles a program in a single fixpoint-free pass, at the width its
    /// branches declare (OCaml compiles max-pv<=1 programs at width 1).
    pub fn compile(branches: Vec<RecordedProgramBranch>) -> Result<Self, RecordedProveError> {
        if Self::shape_width(&branches) <= 1 {
            RecordedCompiledProgramShaped::<RECORDED_N1_STEP_STMT_LEN, 1>::compile(branches)
                .map(Self::W1)
        } else {
            RecordedCompiledProgramShaped::<RECORDED_N2_STEP_STMT_LEN, 2>::compile(branches)
                .map(Self::W2)
        }
    }

    /// See [`RecordedCompiledProgramShaped::debug_compile_stage`].
    #[doc(hidden)]
    pub fn debug_compile_stage(
        branches: Vec<RecordedProgramBranch>,
        stage: usize,
    ) -> Result<String, RecordedProveError> {
        if Self::shape_width(&branches) <= 1 {
            RecordedCompiledProgramShaped::<RECORDED_N1_STEP_STMT_LEN, 1>::debug_compile_stage(
                branches, stage,
            )
        } else {
            RecordedCompiledProgramShaped::<RECORDED_N2_STEP_STMT_LEN, 2>::debug_compile_stage(
                branches, stage,
            )
        }
    }

    /// See [`RecordedCompiledProgramShaped::compile_multipass_reference`].
    #[doc(hidden)]
    pub fn compile_multipass_reference(
        branches: Vec<RecordedProgramBranch>,
    ) -> Result<Self, RecordedProveError> {
        RecordedCompiledProgramShaped::<RECORDED_N2_STEP_STMT_LEN, 2>::compile_multipass_reference(
            branches,
        )
        .map(Self::W2)
    }

    /// A stable cache key for a program's prover indexes (the o1js Cache
    /// header id), covering every branch circuit, width and this format's
    /// version.
    pub fn cache_key(branches: &[RecordedProgramBranch]) -> String {
        let digest = recorded_program_branches_digest(branches);
        let hex = digest
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        format!("recorded-program-v{RECORDED_PROGRAM_CACHE_VERSION}-{hex}")
    }

    /// Serializes the compiled prover indexes (per-branch steps + shared
    /// wrap) for the o1js prover-key cache — everything else is
    /// reconstructed cheaply at [`Self::from_cache_bytes`].
    pub fn to_cache_bytes(&self) -> Result<Vec<u8>, String> {
        with_program_shape!(self, p => p.to_cache_bytes())
    }

    /// Rebuilds a compiled program from cached prover indexes: the
    /// constraint systems are re-synthesized (cheap) and the committed
    /// polynomials come from the cache — the jsoo warm-compile shape.
    pub fn from_cache_bytes(
        branches: Vec<RecordedProgramBranch>,
        bytes: &[u8],
    ) -> Result<Self, RecordedProveError> {
        if Self::shape_width(&branches) <= 1 {
            RecordedCompiledProgramShaped::<RECORDED_N1_STEP_STMT_LEN, 1>::from_cache_bytes(
                branches, bytes,
            )
            .map(Self::W1)
        } else {
            RecordedCompiledProgramShaped::<RECORDED_N2_STEP_STMT_LEN, 2>::from_cache_bytes(
                branches, bytes,
            )
            .map(Self::W2)
        }
    }

    #[doc(hidden)]
    pub fn wrap_branches_for_tests(&self) -> &[crate::api::WrapBranchData] {
        with_program_shape!(self, p => p.wrap_branches_for_tests())
    }

    #[doc(hidden)]
    pub fn wrap_gate_labels_for_tests(&self, from: usize, to: usize) -> Vec<(usize, String)> {
        with_program_shape!(self, p => p.wrap_gate_labels_for_tests(from, to))
    }

    pub fn wrap_verification_key_points(&self) -> Vec<(Fp, Fp)> {
        with_program_shape!(self, p => p.wrap_verification_key_points())
    }

    pub fn verification_key_envelope(&self) -> Result<(String, String), RecordedProveError> {
        with_program_shape!(self, p => p.verification_key_envelope())
    }

    pub fn branch_count(&self) -> usize {
        with_program_shape!(self, p => p.branch_count())
    }

    /// The declared `proofs_verified` of a branch.
    pub fn branch_proofs_verified(&self, branch_index: usize) -> Option<u8> {
        with_program_shape!(self, p => p.branch_proofs_verified(branch_index))
    }

    pub fn prove_n0(
        &mut self,
        branch_index: usize,
        witness: Vec<Fp>,
    ) -> Result<RecordedProofHandle, RecordedProveError> {
        with_program_shape!(self, p => p.prove_n0(branch_index, witness))
    }

    pub fn prove_n1(
        &mut self,
        branch_index: usize,
        previous: &RecordedProofHandle,
        witness: Vec<Fp>,
    ) -> Result<RecordedProofHandle, RecordedProveError> {
        with_program_shape!(self, p => p.prove_n1(branch_index, previous, witness))
    }

    pub fn prove_n2(
        &mut self,
        branch_index: usize,
        previous: [&RecordedProofHandle; 2],
        witness: Vec<Fp>,
    ) -> Result<RecordedProofHandle, RecordedProveError> {
        with_program_shape!(self, p => p.prove_n2(branch_index, previous, witness))
    }

    #[doc(hidden)]
    pub fn debug_prove_recursive_stage(
        &mut self,
        branch_index: usize,
        previous: &[&RecordedProofHandle],
        witness: Vec<Fp>,
        stage: usize,
    ) -> Result<String, RecordedProveError> {
        with_program_shape!(
            self,
            p => p.debug_prove_recursive_stage(branch_index, previous, witness, stage)
        )
    }
}

#[allow(private_bounds)]
impl<const STEP_PI: usize, const ACTIVE: usize> RecordedCompiledProgramShaped<STEP_PI, ACTIVE>
where
    RecordedBootstrapStepShaped<STEP_PI, ACTIVE>: ProgramTemplateDummies,
{
    /// Compiles a program in a single fixpoint-free pass.
    ///
    /// The step and wrap circuits only exchange VALUES (verification-key
    /// commitments, digests) through witness slots and structural parameters
    /// (domains, shifts, linearization tokens) through the alignment helpers.
    /// The structural parameters are invariant under the branch VK values, so
    /// one steps pass aligned to a structure-donor wrap plus one final wrap
    /// compile reproduces exactly what the multi-pass fixpoint iteration
    /// converged to (see `compile_multipass_reference` and the
    /// `program_single_pass_matches_multipass_reference` test).
    pub fn compile(branches: Vec<RecordedProgramBranch>) -> Result<Self, RecordedProveError> {
        Self::compile_with_debug_stage(branches, None)
    }

    /// Debug bisection: runs the single-pass compile up to `stage` (1-based
    /// phase index) and returns the accumulated phase timings as an error
    /// string prefixed with `DEBUG-STAGE`. For locating wasm hangs.
    #[doc(hidden)]
    pub fn debug_compile_stage(
        branches: Vec<RecordedProgramBranch>,
        stage: usize,
    ) -> Result<String, RecordedProveError> {
        match Self::compile_with_debug_stage(branches, Some(stage)) {
            Err(RecordedProveError::Program(message)) if message.starts_with("DEBUG-STAGE") => {
                Ok(message)
            }
            Err(err) => Err(err),
            Ok(_) => Ok(format!("DEBUG-STAGE {stage}: full compile finished")),
        }
    }

    fn compile_with_debug_stage(
        branches: Vec<RecordedProgramBranch>,
        debug_stage: Option<usize>,
    ) -> Result<Self, RecordedProveError> {
        if branches.is_empty() {
            return Err(RecordedProveError::Program(
                "recorded program has no branches".into(),
            ));
        }
        for branch in &branches {
            branch.circuit.validate()?;
            if branch.witness.len() != branch.circuit.aux_count as usize {
                return Err(RecordedProveError::Circuit(
                    RecordedCircuitError::WrongWitnessLength(branch.witness.len()),
                ));
            }
            if branch.proofs_verified > 2 {
                return Err(RecordedProveError::Program(
                    "proofs_verified must be 0, 1 or 2".into(),
                ));
            }
            if usize::from(branch.proofs_verified) > ACTIVE {
                return Err(RecordedProveError::Program(format!(
                    "branch proofs_verified {} exceeds the program shape width {ACTIVE}",
                    branch.proofs_verified
                )));
            }
        }

        let profile = std::env::var_os("PICKLES_PROFILE").is_some();
        let mut phase_timings: Vec<String> = Vec::new();
        let mut phase_index = 0usize;
        macro_rules! phase {
            ($label:expr, $body:expr) => {{
                let t = snarky::wasm_instant::Instant::now();
                let out = $body;
                if profile {
                    eprintln!("[program compile] {}: {:.2?}", $label, t.elapsed());
                }
                phase_index += 1;
                phase_timings.push(format!("{}: {:.2?}", $label, t.elapsed()));
                if debug_stage == Some(phase_index) {
                    let probe = take_probe_timings();
                    return Err(RecordedProveError::Program(format!(
                        "DEBUG-STAGE {phase_index} OK — {} || probe: {}",
                        phase_timings.join(" | "),
                        probe.join(" | ")
                    )));
                }
                out
            }};
        }

        // Template base cycle + bootstrap width-2 step proof: proof-shaped
        // values for every preparation below (and, as a byproduct, the real
        // recursive-step index whose structure seeds the placeholder branch
        // data). Their concrete values never reach a circuit constant, so the
        // embedded dummies (OCaml `Pickles.Dummy` parity) are equivalent to
        // proving live — the live manufacture only remains as the fallback
        // and the blob generator.
        let (template, bootstrap_step) = phase!(
            "template dummies",
            <RecordedBootstrapStepShaped<STEP_PI, ACTIVE> as ProgramTemplateDummies>::template_dummies()
        );

        // Structure-donor wrap: compiled from branch data whose VALUES are
        // placeholders (the bootstrap recursive-step index, which has the
        // real program-step shape). Only its structural fields are consumed
        // by the step alignment, and those are invariant under branch data.
        let mut prepared_wrap = crate::recursive_step::prepare_recursive_wrap_n0_arity::<
            RecordedProgramTemplateApp,
            16,
            40,
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            STEP_PI,
            RECORDED_N2_STEP_ROUNDS,
            RECORDED_N2_WRAP_STMT_LEN,
            ACTIVE,
        >(
            &template,
            &bootstrap_step,
            &recorded_slot_local_max(&branches, ACTIVE),
        );
        prepared_wrap.data.which_branch = 0;
        prepared_wrap.data.branches = branches
            .iter()
            .map(|branch| {
                crate::api::WrapBranchData::from_step_verifier(
                    &bootstrap_step.verifier.index,
                    branch.proofs_verified as usize,
                )
            })
            .collect();
        prepared_wrap.domain_log2 = 0; // natural wrap domain (jsoo Wrap_domains fixpoint)
        let structure_wrap = phase!("wrap structure index", {
            // The natural wrap domain depends on the statement sizes (it sits
            // near the 2^14/2^15 boundary), so probe it from the constraint
            // system alone — no SRS work, no polynomial commitments.
            use snarky::api::SnarkyCircuit as _;
            let donor_domain_log2 = crate::api::WrapCircuit::<
                RECORDED_N2_STEP_ROUNDS,
                RECORDED_N2_WRAP_STMT_LEN,
            > {
                w: Some(prepared_wrap.data.clone()),
            }
            .domain_log2()
            .expect("wrap domain probe");
            synthetic_structure_wrap_index(donor_domain_log2)
        });
        let structure_vk = crate::api::wrap_verification_key_points(&structure_wrap);

        // Probe every branch's natural step domain (OCaml `Fix_domains`, at
        // rough placeholder domains): constraint systems only, no SRS work.
        // The probed domains fix the wrap's per-branch x_hat Lagrange
        // constants *and* the unique-domain list the steps' finalize
        // one-hot selects over, before anything expensive compiles.
        let branch_domain_log2s: Vec<u32> = phase!("step domain probe", {
            // Three width-2 synthesis probes in parallel exhaust the wasm32
            // linear memory / allocator; run them sequentially there (they
            // are seconds each), in parallel on native.
            if cfg!(target_arch = "wasm32") {
                branches
                    .iter()
                    .map(|branch| {
                        recorded_program_step_branch_domain_log2::<STEP_PI, ACTIVE>(
                            branch,
                            &template,
                            &structure_vk,
                            &structure_wrap.index,
                        )
                    })
                    .collect()
            } else {
                use rayon::prelude::*;
                branches
                    .par_iter()
                    .map(|branch| {
                        recorded_program_step_branch_domain_log2::<STEP_PI, ACTIVE>(
                            branch,
                            &template,
                            &structure_vk,
                            &structure_wrap.index,
                        )
                    })
                    .collect()
            }
        });
        let finalize_domain_log2s: Vec<u32> = {
            let mut list = branch_domain_log2s.clone();
            list.sort_unstable();
            list.dedup();
            list
        };
        if profile {
            eprintln!(
                "[program compile] probed step domains: {branch_domain_log2s:?} (unique {finalize_domain_log2s:?})"
            );
        }

        // Single steps pass against the structure wrap: the wrap VK enters
        // the step data as WITNESS values only (the step indexes are stable
        // under wrap VK values), so compiling against the donor is safe. The
        // first N0 branch compiles without finalize alignment (aligning it
        // to its own index is a no-op), every other branch aligns to that
        // shared finalize index.
        let step_indexes = phase!(
            "steps compile",
            compile_recorded_program_steps_single_pass::<STEP_PI, ACTIVE>(
                &branches,
                &template,
                &structure_vk,
                &structure_wrap.index,
                &finalize_domain_log2s,
            )
        );
        let wrap_branches = recorded_program_wrap_branches(&branches, &step_indexes);
        for (i, indexes) in step_indexes.iter().enumerate() {
            let compiled_log2 = indexes
                .as_ref()
                .expect("compiled branch step")
                .1
                .index
                .domain
                .log_size_of_group;
            assert_eq!(
                compiled_log2, branch_domain_log2s[i],
                "branch {i}: compiled step domain diverged from the probe"
            );
        }

        // Final wrap: OCaml's `choose_key` bakes the branch step VKs as
        // circuit CONSTANTS, so the shared wrap must compile after the steps
        // with the real branch data. The per-branch x_hat Lagrange constants
        // come from the probed domains (equal to each step index's own —
        // asserted above through the domain check). With equal branch
        // domains they collapse to constants in-circuit (OCaml's all-equal
        // shortcut), otherwise the which_branch one-hot selects.
        prepared_wrap.data.branches = wrap_branches.clone();
        let wrap_statement_lagranges: Vec<Vec<_>> = branch_domain_log2s
            .iter()
            .map(|&log2| {
                crate::recursive_step::step_statement_lagranges_for_domain(
                    log2,
                    &prepared_wrap.data.step_statement,
                )
            })
            .collect();
        prepared_wrap.data.step_statement_lagranges = wrap_statement_lagranges.clone();
        let prepared_wrap = crate::recursive_step::align_program_recursive_wrap_finalize_index(
            prepared_wrap,
            &structure_wrap.index,
        );
        let wrap_indexes = phase!(
            "wrap final compile",
            crate::recursive_step::compile_prepared_recursive_wrap(&prepared_wrap)
        );

        // Guard the single-pass premise: swapping branch VK values must not
        // move any structural field the alignments consume. A violation here
        // means the steps were aligned against the wrong wrap structure.
        {
            let donor = &structure_wrap.index;
            let fixed = &wrap_indexes.1.index;
            assert_eq!(
                fixed.domain, donor.domain,
                "wrap domain changed under branch VK values"
            );
            assert_eq!(
                fixed.max_poly_size, donor.max_poly_size,
                "wrap SRS size changed under branch VK values"
            );
            assert_eq!(
                fixed.shift, donor.shift,
                "wrap shifts changed under branch VK values"
            );
            assert_eq!(
                fixed.endo, donor.endo,
                "wrap endo changed under branch VK values"
            );
        }

        // The stored template pads unfilled proof slots at prove time. Its
        // values are witness-only there — dummy slots are masked and their
        // messages travel inside each proof — so the embedded/bootstrap
        // template serves as well as one re-proved against the final wrap
        // key. OCaml pads with the same fixed `Pickles.Dummy` values for
        // every program and never proves at compile time.
        let template = phase!("final template prove", template);

        Ok(Self {
            branches,
            wrap_branches,
            wrap_statement_lagranges,
            finalize_domain_log2s,
            step_indexes,
            wrap_indexes: Some(wrap_indexes),
            template,
        })
    }

}

impl RecordedCompiledProgramShaped<RECORDED_N2_STEP_STMT_LEN, 2> {
    /// The historical multi-pass fixpoint compile, kept as the reference the
    /// single-pass `compile` is tested against. Do not use outside tests.
    #[doc(hidden)]
    pub fn compile_multipass_reference(
        branches: Vec<RecordedProgramBranch>,
    ) -> Result<Self, RecordedProveError> {
        if branches.is_empty() {
            return Err(RecordedProveError::Program(
                "recorded program has no branches".into(),
            ));
        }
        for branch in &branches {
            branch.circuit.validate()?;
            if branch.witness.len() != branch.circuit.aux_count as usize {
                return Err(RecordedProveError::Circuit(
                    RecordedCircuitError::WrongWitnessLength(branch.witness.len()),
                ));
            }
            if branch.proofs_verified > 2 {
                return Err(RecordedProveError::Program(
                    "proofs_verified must be 0, 1 or 2".into(),
                ));
            }
        }

        let profile = std::env::var_os("PICKLES_PROFILE").is_some();
        macro_rules! phase {
            ($label:expr, $body:expr) => {{
                let t = snarky::wasm_instant::Instant::now();
                let out = $body;
                if profile {
                    eprintln!("[program compile] {}: {:.2?}", $label, t.elapsed());
                }
                out
            }};
        }

        crate::common::warm_recursion_caches(true);
        // A protocol-only valid proof supplies proof-shaped values while Step
        // indexes are compiled from the real application circuits. No user
        // witness has to satisfy its constraints during program compilation.
        let mut template_compiled = phase!(
            "template base compile",
            crate::api::CompiledBaseCase::<RecordedProgramTemplateApp, 16, 40>::compile(
                RecordedProgramTemplateApp,
                (),
            )
        );
        let template = phase!("template base prove #1", template_compiled.prove(()));
        let bootstrap_vk = crate::api::wrap_verification_key_points(&template.wrap_verifier);

        let branch_domain_log2s: Vec<u32> = phase!("step domain probe", {
            use rayon::prelude::*;
            branches
                .par_iter()
                .map(|branch| {
                    recorded_program_step_branch_domain_log2::<RECORDED_N2_STEP_STMT_LEN, 2>(
                        branch,
                        &template,
                        &bootstrap_vk,
                        &template.wrap_verifier.index,
                    )
                })
                .collect()
        });
        let finalize_domain_log2s: Vec<u32> = {
            let mut list = branch_domain_log2s.clone();
            list.sort_unstable();
            list.dedup();
            list
        };

        let step_indexes = phase!(
            "steps pass #1",
            compile_recorded_program_steps::<RECORDED_N2_STEP_STMT_LEN, 2>(
                &branches,
                &template,
                &bootstrap_vk,
                &template.wrap_verifier.index,
                None,
                &finalize_domain_log2s,
            )
        );
        let wrap_branches = recorded_program_wrap_branches(&branches, &step_indexes);

        let bootstrap = crate::recursive_step::prepare_recursive_step_with_state::<
            RecordedProgramTemplateApp,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            40,
            RECORDED_N1_STEP_STMT_LEN,
        >(
            &template,
            bootstrap_vk,
            vec![Fp::from(0u64)],
            vec![Fp::from(0u64)],
        );
        let bootstrap = crate::recursive_step::normalize_program_recursive_step(bootstrap);
        let bootstrap = crate::recursive_step::prepare_recursive_step_n0::<
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N2_STEP_STMT_LEN,
        >(bootstrap, vec![Fp::from(0u64)]);
        let bootstrap_step = phase!(
            "bootstrap N2 step prove",
            crate::recursive_step::prove_recursive_step_width2::<
                RECORDED_N1_STEP_ROUNDS,
                RECORDED_BASE_WRAP_ROUNDS,
                RECORDED_N1_STEP_STMT_LEN,
                RECORDED_N2_STEP_STMT_LEN,
            >(bootstrap)
        );
        let mut prepared_wrap = crate::recursive_step::prepare_recursive_wrap_n0::<
            RecordedProgramTemplateApp,
            16,
            40,
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            RECORDED_N2_STEP_STMT_LEN,
            RECORDED_N2_STEP_ROUNDS,
            RECORDED_N2_WRAP_STMT_LEN,
        >(&template, &bootstrap_step);
        prepared_wrap.data.which_branch = 0;
        prepared_wrap.data.branches = wrap_branches.clone();
        prepared_wrap.domain_log2 = 0; // natural wrap domain (jsoo Wrap_domains fixpoint)
        let first_wrap_indexes = phase!(
            "wrap compile #1",
            crate::recursive_step::compile_prepared_recursive_wrap(&prepared_wrap)
        );
        let first_wrap_vk = crate::api::wrap_verification_key_points(&first_wrap_indexes.1);
        let first_template = phase!(
            "template base prove #2",
            crate::api::prove_base_case::<RecordedProgramTemplateApp, 16, 40>(
                RecordedProgramTemplateApp,
                (),
                first_wrap_vk.clone(),
            )
        );
        let second_step_indexes = phase!(
            "steps pass #2",
            compile_recorded_program_steps::<RECORDED_N2_STEP_STMT_LEN, 2>(
                &branches,
                &first_template,
                &first_wrap_vk,
                &first_wrap_indexes.1.index,
                None,
                &finalize_domain_log2s,
            )
        );
        let second_wrap_branches = recorded_program_wrap_branches(&branches, &second_step_indexes);
        if profile {
            eprintln!(
                "[program compile] steps #2 VKs == steps #1 VKs: {}",
                second_wrap_branches == wrap_branches
            );
        }
        prepared_wrap.data.branches = second_wrap_branches.clone();
        let wrap_indexes = phase!(
            "wrap compile #2",
            crate::recursive_step::compile_prepared_recursive_wrap(&prepared_wrap)
        );
        let final_wrap_vk = crate::api::wrap_verification_key_points(&wrap_indexes.1);
        if profile {
            eprintln!(
                "[program compile] wrap #2 VK == wrap #1 VK: {}",
                final_wrap_vk == first_wrap_vk
            );
        }
        let template = phase!(
            "template base prove #3",
            crate::api::prove_base_case::<RecordedProgramTemplateApp, 16, 40>(
                RecordedProgramTemplateApp,
                (),
                final_wrap_vk.clone(),
            )
        );
        let finalize_index = branches
            .iter()
            .zip(&second_step_indexes)
            .find(|(branch, _)| branch.proofs_verified == 0)
            .and_then(|(_, indexes)| indexes.as_ref())
            .map(|indexes| &indexes.1.index);
        let step_indexes = phase!(
            "steps pass #3",
            compile_recorded_program_steps::<RECORDED_N2_STEP_STMT_LEN, 2>(
                &branches,
                &template,
                &final_wrap_vk,
                &wrap_indexes.1.index,
                finalize_index,
                &finalize_domain_log2s,
            )
        );
        let wrap_branches = recorded_program_wrap_branches(&branches, &step_indexes);
        if profile {
            for (i, (a, b)) in wrap_branches.iter().zip(&second_wrap_branches).enumerate() {
                eprintln!(
                    "[program compile] steps #3 branch {i} (pv={}) == steps #2: {}",
                    branches[i].proofs_verified,
                    a == b
                );
            }
        }
        prepared_wrap.data.branches = wrap_branches.clone();
        let wrap_statement_lagranges: Vec<Vec<_>> = step_indexes
            .iter()
            .map(|indexes| {
                crate::recursive_step::step_statement_lagranges_for_index(
                    &indexes.as_ref().expect("compiled branch step").1.index,
                    &prepared_wrap.data.step_statement,
                )
            })
            .collect();
        prepared_wrap.data.step_statement_lagranges = wrap_statement_lagranges.clone();
        let prepared_wrap = crate::recursive_step::align_program_recursive_wrap_finalize_index(
            prepared_wrap,
            &wrap_indexes.1.index,
        );
        let wrap_indexes = phase!(
            "wrap compile #3",
            crate::recursive_step::compile_prepared_recursive_wrap(&prepared_wrap)
        );
        let final_wrap_vk2 = crate::api::wrap_verification_key_points(&wrap_indexes.1);
        if profile {
            eprintln!(
                "[program compile] wrap #3 VK == wrap #2 VK: {}",
                final_wrap_vk2 == final_wrap_vk
            );
        }
        let final_wrap_vk = final_wrap_vk2;
        let template = phase!(
            "template base prove #4",
            crate::api::prove_base_case::<RecordedProgramTemplateApp, 16, 40>(
                RecordedProgramTemplateApp,
                (),
                final_wrap_vk.clone(),
            )
        );
        let finalize_index = branches
            .iter()
            .zip(&step_indexes)
            .find(|(branch, _)| branch.proofs_verified == 0)
            .and_then(|(_, indexes)| indexes.as_ref())
            .map(|indexes| &indexes.1.index);
        let stable_step_indexes = phase!(
            "steps pass #4",
            compile_recorded_program_steps::<RECORDED_N2_STEP_STMT_LEN, 2>(
                &branches,
                &template,
                &final_wrap_vk,
                &wrap_indexes.1.index,
                finalize_index,
                &finalize_domain_log2s,
            )
        );
        let stable_wrap_branches = recorded_program_wrap_branches(&branches, &stable_step_indexes);
        assert_eq!(
            stable_wrap_branches, wrap_branches,
            "Step verification keys did not stabilize under the final shared Wrap key"
        );

        Ok(Self {
            branches,
            wrap_branches,
            wrap_statement_lagranges,
            finalize_domain_log2s,
            step_indexes: stable_step_indexes,
            wrap_indexes: Some(wrap_indexes),
            template,
        })
    }

}

#[allow(private_bounds)]
impl<const STEP_PI: usize, const ACTIVE: usize> RecordedCompiledProgramShaped<STEP_PI, ACTIVE>
where
    RecordedProgramCycleShaped<STEP_PI, ACTIVE>: ProgramCycleSlot,
    RecordedBootstrapStepShaped<STEP_PI, ACTIVE>: ProgramTemplateDummies,
{
    pub fn to_cache_bytes(&self) -> Result<Vec<u8>, String> {
        let mut step_verifiers = Vec::with_capacity(self.step_indexes.len());
        for indexes in &self.step_indexes {
            let pair = indexes
                .as_ref()
                .ok_or_else(|| "compiled Step index is temporarily in use".to_string())?;
            step_verifiers.push(rmp_serde::to_vec(&pair.1.index).map_err(|err| err.to_string())?);
        }
        let wrap = self
            .wrap_indexes
            .as_ref()
            .ok_or_else(|| "compiled Wrap index is temporarily in use".to_string())?;
        let wrap_verifier = rmp_serde::to_vec(&wrap.1.index).map_err(|err| err.to_string())?;
        rmp_serde::to_vec(&RecordedProgramIndexCache {
            version: RECORDED_PROGRAM_CACHE_VERSION,
            branches_digest: recorded_program_branches_digest(&self.branches),
            step_verifiers,
            wrap_verifier,
        })
        .map_err(|err| err.to_string())
    }

    /// The warm-compile path: constraint systems are re-synthesized against
    /// the SAME preparation flow as [`Self::compile`], and the cached
    /// committed polynomials replace the expensive index builds.
    pub fn from_cache_bytes(
        branches: Vec<RecordedProgramBranch>,
        bytes: &[u8],
    ) -> Result<Self, RecordedProveError> {
        let fail = |message: String| RecordedProveError::Program(message);
        for branch in &branches {
            branch.circuit.validate()?;
            if branch.witness.len() != branch.circuit.aux_count as usize {
                return Err(RecordedProveError::Circuit(
                    RecordedCircuitError::WrongWitnessLength(branch.witness.len()),
                ));
            }
            if usize::from(branch.proofs_verified) > ACTIVE {
                return Err(fail(format!(
                    "branch proofs_verified {} exceeds the program shape width {ACTIVE}",
                    branch.proofs_verified
                )));
            }
        }
        let cache: RecordedProgramIndexCache =
            rmp_serde::from_slice(bytes).map_err(|err| fail(err.to_string()))?;
        if cache.version != RECORDED_PROGRAM_CACHE_VERSION
            || cache.branches_digest != recorded_program_branches_digest(&branches)
        {
            return Err(fail(
                "cached indexes belong to a different program or version".into(),
            ));
        }
        if cache.step_verifiers.len() != branches.len() {
            return Err(fail("cached step index count mismatch".into()));
        }

        let (template, bootstrap_step) =
            <RecordedBootstrapStepShaped<STEP_PI, ACTIVE> as ProgramTemplateDummies>::template_dummies();

        // Restore the raw kimchi verifier indexes.
        let mut step_raws = Vec::with_capacity(cache.step_verifiers.len());
        for bytes in &cache.step_verifiers {
            let raw: RecordedRawStepVerifier =
                rmp_serde::from_slice(bytes).map_err(|err| fail(err.to_string()))?;
            step_raws.push(restore_step_verifier(raw));
        }
        let wrap_raw: RecordedRawWrapVerifier =
            rmp_serde::from_slice(&cache.wrap_verifier).map_err(|err| fail(err.to_string()))?;
        let wrap_raw = restore_wrap_verifier(wrap_raw);

        // Structural donor at the cached wrap domain (same alignment source
        // as the single-pass compile).
        let wrap_domain_log2 = wrap_raw.domain.log_size_of_group;
        let structure_wrap = synthetic_structure_wrap_index(wrap_domain_log2);
        // The steps re-synthesize against the SAME donor values as the
        // single-pass compile (wrap keys are witness-only; matching the
        // compile keeps the gate stream byte-identical to the cached one).
        let structure_vk = crate::api::wrap_verification_key_points(&structure_wrap);
        let branch_domain_log2s: Vec<u32> = step_raws
            .iter()
            .map(|raw| raw.domain.log_size_of_group)
            .collect();
        let finalize_domain_log2s: Vec<u32> = {
            let mut list = branch_domain_log2s.clone();
            list.sort_unstable();
            list.dedup();
            list
        };


        // Steps: first N0 (its restored verifier is the finalize alignment
        // index for the rest), then the others — the SAME preparation flow
        // as `compile_recorded_program_steps_single_pass`.
        let mut step_raws: Vec<Option<RecordedRawStepVerifier>> =
            step_raws.into_iter().map(Some).collect();
        let mut step_indexes: Vec<Option<RecordedProgramStepIndexesShaped<STEP_PI, ACTIVE>>> =
            (0..branches.len()).map(|_| None).collect();
        let first_n0 = branches.iter().position(|b| b.proofs_verified == 0);
        let restore_branch = |branch: &RecordedProgramBranch,
                              finalize_index: Option<&StepFinalizeIndex>,
                              raw: RecordedRawStepVerifier|
         -> Result<RecordedProgramStepIndexesShaped<STEP_PI, ACTIVE>, RecordedProveError> {
            let (prepared, main) = build_recorded_program_step_prepared::<STEP_PI, ACTIVE>(
                branch,
                &template,
                &structure_vk,
                &structure_wrap.index,
                finalize_index,
                &finalize_domain_log2s,
            );
            crate::recursive_step::restore_prepared_recursive_step_width2_arity::<
                RECORDED_N1_STEP_ROUNDS,
                RECORDED_BASE_WRAP_ROUNDS,
                RECORDED_N1_STEP_STMT_LEN,
                STEP_PI,
                ACTIVE,
            >(&prepared, Some(main), raw)
            .map_err(RecordedProveError::Program)
        };
        if let Some(i) = first_n0 {
            let raw = step_raws[i].take().expect("raw present");
            step_indexes[i] = Some(restore_branch(&branches[i], None, raw)?);
        }
        let finalize_holder = first_n0.map(|i| step_indexes[i].as_ref().expect("set").1.clone());
        let finalize_index = finalize_holder.as_ref().map(|v| &v.index);
        let rest: Vec<usize> = (0..branches.len()).filter(|&i| Some(i) != first_n0).collect();
        let mut raws: Vec<(usize, RecordedRawStepVerifier)> = rest
            .iter()
            .map(|&i| (i, step_raws[i].take().expect("raw present")))
            .collect();
        // Restore the remaining branches in parallel, like the single-pass
        // compile's step phase.
        let restored: Vec<(usize, Result<_, RecordedProveError>)> = {
            use rayon::prelude::*;
            raws.par_drain(..)
                .map(|(i, raw)| (i, restore_branch(&branches[i], finalize_index, raw)))
                .collect()
        };
        for (i, result) in restored {
            step_indexes[i] = Some(result?);
        }
        for (i, indexes) in step_indexes.iter().enumerate() {
            let restored_log2 = indexes
                .as_ref()
                .expect("restored branch step")
                .1
                .index
                .domain
                .log_size_of_group;
            if restored_log2 != branch_domain_log2s[i] {
                return Err(fail(format!(
                    "branch {i}: restored step domain diverged from the cache"
                )));
            }
        }

        // Final wrap, prepared exactly like the single-pass compile.
        let wrap_branches = recorded_program_wrap_branches(&branches, &step_indexes);
        let mut prepared_wrap = crate::recursive_step::prepare_recursive_wrap_n0_arity::<
            RecordedProgramTemplateApp,
            16,
            40,
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            STEP_PI,
            RECORDED_N2_STEP_ROUNDS,
            RECORDED_N2_WRAP_STMT_LEN,
            ACTIVE,
        >(
            &template,
            &bootstrap_step,
            &recorded_slot_local_max(&branches, ACTIVE),
        );
        prepared_wrap.data.which_branch = 0;
        prepared_wrap.data.branches = wrap_branches.clone();
        prepared_wrap.domain_log2 = 0;
        let wrap_statement_lagranges: Vec<Vec<_>> = branch_domain_log2s
            .iter()
            .map(|&log2| {
                crate::recursive_step::step_statement_lagranges_for_domain(
                    log2,
                    &prepared_wrap.data.step_statement,
                )
            })
            .collect();
        prepared_wrap.data.step_statement_lagranges = wrap_statement_lagranges.clone();
        let prepared_wrap = crate::recursive_step::align_program_recursive_wrap_finalize_index(
            prepared_wrap,
            &structure_wrap.index,
        );
        let wrap_indexes =
            crate::recursive_step::restore_prepared_recursive_wrap(&prepared_wrap, wrap_raw)
                .map_err(RecordedProveError::Program)?;


        Ok(Self {
            branches,
            wrap_branches,
            wrap_statement_lagranges,
            finalize_domain_log2s,
            step_indexes,
            wrap_indexes: Some(wrap_indexes),
            template,
        })
    }

    /// The per-branch step verification key data embedded in the shared
    /// wrap. Exposed for the single-pass/multi-pass equivalence test.
    #[doc(hidden)]
    pub fn wrap_branches_for_tests(&self) -> &[crate::api::WrapBranchData] {
        &self.wrap_branches
    }

    /// Emission labels of the shared wrap's gates in `[from, to)` — debug
    /// tooling for locating a failing row.
    #[doc(hidden)]
    pub fn wrap_gate_labels_for_tests(&self, from: usize, to: usize) -> Vec<(usize, String)> {
        let prover = &self.wrap_indexes.as_ref().unwrap().0;
        let labels = prover.gate_labels();
        let gates = &prover.index.cs.gates;
        eprintln!(
            "labels.len()={} gates.len()={} domain=2^{}",
            labels.len(),
            gates.len(),
            prover.index.cs.domain.d1.log_size_of_group
        );
        (from..to.min(gates.len()))
            .map(|i| {
                (
                    i,
                    format!(
                        "{:?} | {}",
                        gates[i].typ,
                        labels.get(i).cloned().unwrap_or_default()
                    ),
                )
            })
            .collect()
    }

    pub fn wrap_verification_key_points(&self) -> Vec<(Fp, Fp)> {
        crate::api::wrap_verification_key_points(&self.wrap_indexes.as_ref().unwrap().1)
    }

    /// The canonical Mina side-loaded verification key of the program — ONE
    /// key shared by every branch (the stable encoding carries only the
    /// shared wrap commitments, `max_proofs_verified` and the actual wrap
    /// domain): the bin_prot bytes base64-encoded and the Mina account-level
    /// hash.
    pub fn verification_key_envelope(&self) -> Result<(String, String), RecordedProveError> {
        use base64::prelude::*;
        // Not part of the stable encoding; recorded for validation only.
        let step_domain_log2 = *self
            .finalize_domain_log2s
            .iter()
            .max()
            .expect("compiled program has step domains") as u8;
        let wrap_verifier = &self.wrap_indexes.as_ref().expect("compiled Wrap indexes").1;
        // The program's declared width is the max over its branches (OCaml
        // `Pickles.compile`), not the width the wrap domain implies.
        let max_proofs_verified = match self
            .branches
            .iter()
            .map(|branch| branch.proofs_verified)
            .max()
            .expect("compiled program has branches")
        {
            0 => crate::composition_types::ProofsVerified::N0,
            1 => crate::composition_types::ProofsVerified::N1,
            _ => crate::composition_types::ProofsVerified::N2,
        };
        let key = crate::side_loaded::SideLoadedVerificationKey::from_wrap_verifier_with_max(
            step_domain_log2,
            wrap_verifier,
            max_proofs_verified,
        )
        .map_err(|err| RecordedProveError::Program(format!("side-loaded key: {err:?}")))?;
        let stable = key.to_stable_v2();
        let base64 = BASE64_STANDARD.encode(
            stable
                .to_bin_prot()
                .map_err(|err| RecordedProveError::Program(format!("VK encoding: {err:?}")))?,
        );
        Ok((base64, stable.mina_hash().to_string()))
    }

    pub fn branch_count(&self) -> usize {
        self.branches.len()
    }

    /// The declared `proofs_verified` of a branch.
    pub fn branch_proofs_verified(&self, branch_index: usize) -> Option<u8> {
        self.branches
            .get(branch_index)
            .map(|branch| branch.proofs_verified)
    }

    pub fn prove_n0(
        &mut self,
        branch_index: usize,
        witness: Vec<Fp>,
    ) -> Result<RecordedProofHandle, RecordedProveError> {
        let branch = self
            .branches
            .get(branch_index)
            .ok_or_else(|| RecordedProveError::Program("unknown program branch".into()))?;
        if branch.proofs_verified != 0 {
            return Err(RecordedProveError::Program(
                "prove_n0 requires an N0 branch".into(),
            ));
        }
        if witness.len() != branch.circuit.aux_count as usize {
            return Err(RecordedProveError::Circuit(
                RecordedCircuitError::WrongWitnessLength(witness.len()),
            ));
        }
        let app_state = branch.circuit.state(&witness);
        let prepared = crate::recursive_step::prepare_recursive_step_with_state::<
            RecordedProgramTemplateApp,
            16,
            RECORDED_BASE_WRAP_ROUNDS,
            40,
            RECORDED_N1_STEP_STMT_LEN,
        >(
            &self.template,
            self.wrap_verification_key_points(),
            vec![Fp::from(0u64); app_state.len()],
            app_state.clone(),
        );
        let prepared = crate::recursive_step::normalize_program_recursive_step(prepared);
        let prepared = crate::recursive_step::align_program_recursive_step_finalize_domains(
            prepared,
            &self.finalize_domain_log2s,
        );
        let prepared = crate::recursive_step::prepare_recursive_step_n0::<
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            STEP_PI,
        >(prepared, app_state.clone());
        let prepared = apply_previous_proof_widths(prepared, branch, ACTIVE);
        let carried_accumulators = prepared
            .messages_for_next_step_proof
            .challenge_polynomial_commitments
            .clone();
        let carried_challenges: Vec<Vec<Fp>> = prepared
            .recursions
            .iter()
            .zip(prepared.dummy_slots)
            .filter(|(_, dummy)| !dummy)
            .map(|(recursion, _)| recursion.chals.clone())
            .collect();
        let dummy_accumulator = crate::dummy::pasta_dummy_wrap_sg();
        let physical_accumulators = prepared
            .proofs
            .iter()
            .zip(prepared.dummy_slots)
            .map(|(proof, dummy)| {
                if dummy {
                    (dummy_accumulator.x, dummy_accumulator.y)
                } else {
                    proof.sg
                }
            })
            .collect();
        let physical_challenges = prepared
            .recursions
            .iter()
            .map(|recursion| recursion.chals.clone())
            .collect();
        let app = RecordedApp {
            circuit: branch.circuit.clone(),
        };
        let main: crate::recursive_step::EmbeddedAppMain =
            std::sync::Arc::new(move |sys, previous_app_state| {
                app.main_with_previous_app_state(sys, Some(&witness), previous_app_state)
            });
        let indexes = self.step_indexes[branch_index]
            .take()
            .expect("compiled program Step indexes");
        let (step, indexes) = crate::recursive_step::prove_prepared_recursive_step_width2_arity(
            prepared,
            Some(main),
            Some(indexes),
        );
        self.step_indexes[branch_index] = Some(indexes);
        let mut prepared_wrap = crate::recursive_step::prepare_recursive_wrap_n0_arity::<
            RecordedProgramTemplateApp,
            16,
            40,
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            STEP_PI,
            RECORDED_N2_STEP_ROUNDS,
            RECORDED_N2_WRAP_STMT_LEN,
            ACTIVE,
        >(
            &self.template,
            &step,
            &recorded_slot_local_max(&self.branches, ACTIVE),
        );
        prepared_wrap.data.which_branch = branch_index;
        prepared_wrap.data.branches = self.wrap_branches.clone();
        prepared_wrap.data.step_statement_lagranges = self.wrap_statement_lagranges.clone();
        prepared_wrap.domain_log2 = 0; // natural wrap domain (jsoo Wrap_domains fixpoint)
        let prepared_wrap = crate::recursive_step::align_program_recursive_wrap_finalize_index(
            prepared_wrap,
            &self
                .wrap_indexes
                .as_ref()
                .expect("compiled program Wrap indexes")
                .1
                .index,
        );
        let indexes = self
            .wrap_indexes
            .take()
            .expect("compiled program Wrap indexes");
        let (wrap, indexes) =
            crate::recursive_step::prove_prepared_recursive_wrap(prepared_wrap, Some(indexes));
        self.wrap_indexes = Some(indexes);
        let proof = wrap
            .to_mina_network_proof(step.verifier.index.domain.log_size_of_group as u8)
            .map_err(RecordedProveError::RecursiveBackend)?;
        Ok(RecordedProofHandle {
            app_state,
            proof,
            inner: RecordedProgramCycleShaped {
                step,
                wrap,
                carried_accumulators,
                carried_challenges,
                physical_accumulators,
                physical_challenges,
                proofs_verified: 0,
            }
            .into_inner(),
        })
    }

    pub fn prove_n1(
        &mut self,
        branch_index: usize,
        previous: &RecordedProofHandle,
        witness: Vec<Fp>,
    ) -> Result<RecordedProofHandle, RecordedProveError> {
        self.prove_recursive(branch_index, std::slice::from_ref(&previous), witness)
    }

    pub fn prove_n2(
        &mut self,
        branch_index: usize,
        previous: [&RecordedProofHandle; 2],
        witness: Vec<Fp>,
    ) -> Result<RecordedProofHandle, RecordedProveError> {
        self.prove_recursive(branch_index, &previous, witness)
    }

    /// Debug bisection of a recursive program prove: runs up to `stage`
    /// (1 = previous prepared, 2 = step prepared, 3 = step proved,
    /// 4 = wrap prepared, 5+ = full) and reports the timings.
    #[doc(hidden)]
    pub fn debug_prove_recursive_stage(
        &mut self,
        branch_index: usize,
        previous: &[&RecordedProofHandle],
        witness: Vec<Fp>,
        stage: usize,
    ) -> Result<String, RecordedProveError> {
        match self.prove_recursive_impl(branch_index, previous, witness, Some(stage)) {
            Err(RecordedProveError::Program(message)) if message.starts_with("DEBUG-STAGE") => {
                Ok(message)
            }
            Err(err) => Err(err),
            Ok(_) => Ok(format!("DEBUG-STAGE {stage}: full prove finished")),
        }
    }

    fn prove_recursive(
        &mut self,
        branch_index: usize,
        previous: &[&RecordedProofHandle],
        witness: Vec<Fp>,
    ) -> Result<RecordedProofHandle, RecordedProveError> {
        self.prove_recursive_impl(branch_index, previous, witness, None)
    }

    fn prove_recursive_impl(
        &mut self,
        branch_index: usize,
        previous: &[&RecordedProofHandle],
        witness: Vec<Fp>,
        debug_stage: Option<usize>,
    ) -> Result<RecordedProofHandle, RecordedProveError> {
        let prove_started = snarky::wasm_instant::Instant::now();
        let mut stage_timings: Vec<String> = Vec::new();
        let mut stage_index = 0usize;
        macro_rules! prove_stage {
            ($label:expr) => {{
                stage_index += 1;
                stage_timings.push(format!("{}: {:.2?}", $label, prove_started.elapsed()));
                if debug_stage == Some(stage_index) {
                    return Err(RecordedProveError::Program(format!(
                        "DEBUG-STAGE {stage_index} OK — {}",
                        stage_timings.join(" | ")
                    )));
                }
            }};
        }
        let branch = self
            .branches
            .get(branch_index)
            .ok_or_else(|| RecordedProveError::Program("unknown program branch".into()))?;
        if usize::from(branch.proofs_verified) != previous.len() || previous.is_empty() {
            return Err(RecordedProveError::Program(format!(
                "branch expects {} previous proofs, got {}",
                branch.proofs_verified,
                previous.len()
            )));
        }
        if witness.len() != branch.circuit.aux_count as usize {
            return Err(RecordedProveError::Circuit(
                RecordedCircuitError::WrongWitnessLength(witness.len()),
            ));
        }
        let shared_wrap_vk = self.wrap_verification_key_points();
        let mut previous_cycles = Vec::with_capacity(previous.len());
        for proof in previous {
            let Some(cycle) =
                <RecordedProgramCycleShaped<STEP_PI, ACTIVE> as ProgramCycleSlot>::from_inner(
                    &proof.inner,
                )
            else {
                return Err(RecordedProveError::Program(
                    "program branches require proofs from a compiled program".into(),
                ));
            };
            if cycle.step.messages_for_next_step_vk_pts != shared_wrap_vk
                || crate::api::wrap_verification_key_points(&cycle.wrap.verifier) != shared_wrap_vk
            {
                return Err(RecordedProveError::Program(
                    "previous proof uses a different program Wrap key".into(),
                ));
            }
            previous_cycles.push((proof, cycle));
        }

        prove_stage!("previous checked");
        // A recorded o1js rule lays out `publicInput` first, followed by the
        // public input/output state of each previous proof. Those values are
        // dynamic: the branch witness used while compiling is only a shape
        // witness. Keep the prove-time witness synchronized with the actual
        // recursive statements before evaluating the new application state.
        let previous_app_values: Vec<Fp> = previous_cycles
            .iter()
            .flat_map(|(proof, _)| proof.app_state.iter().copied())
            .collect();
        let mut witness = witness;
        let app = RecordedApp {
            circuit: branch.circuit.clone(),
        };
        if app.has_program_previous_state_slots(previous_app_values.len()) {
            witness[1..].copy_from_slice(&previous_app_values);
        }
        let app_state = branch.circuit.state(&witness);
        let mut prepared_previous = Vec::with_capacity(previous.len());
        for (proof, cycle) in &previous_cycles {
            prepared_previous.push(
                crate::recursive_step::prepare_program_recursive_step_from_previous::<
                    RECORDED_N1_STEP_ROUNDS,
                    RECORDED_BASE_WRAP_ROUNDS,
                    RECORDED_N1_STEP_STMT_LEN,
                    STEP_PI,
                    RECORDED_N2_WRAP_STMT_LEN,
                    RECORDED_N1_STEP_STMT_LEN,
                    ACTIVE,
                >(
                    &cycle.step,
                    &cycle.wrap,
                    cycle.physical_accumulators.clone(),
                    cycle.physical_challenges.clone(),
                    shared_wrap_vk.clone(),
                    proof.app_state.clone(),
                    app_state.clone(),
                ),
            );
        }
        let prepared_previous: Vec<_> = prepared_previous
            .into_iter()
            .map(|prepared| {
                crate::recursive_step::align_program_recursive_step_finalize_domains(
                    prepared,
                    &self.finalize_domain_log2s,
                )
            })
            .collect();
        let mut prepared_previous = prepared_previous.into_iter();
        let prepared = match previous.len() {
            1 => crate::recursive_step::prepare_recursive_step_n1::<
                RECORDED_BASE_WRAP_ROUNDS,
                RECORDED_N1_STEP_STMT_LEN,
                STEP_PI,
            >(prepared_previous.next().unwrap(), app_state.clone()),
            2 => crate::recursive_step::prepare_recursive_step_width2::<
                RECORDED_BASE_WRAP_ROUNDS,
                RECORDED_N1_STEP_STMT_LEN,
                STEP_PI,
            >(
                prepared_previous.next().unwrap(),
                prepared_previous.next().unwrap(),
                app_state.clone(),
            ),
            _ => unreachable!(),
        };
        let prepared = apply_previous_proof_widths(prepared, branch, ACTIVE);
        let carried_accumulators = prepared
            .messages_for_next_step_proof
            .challenge_polynomial_commitments
            .clone();
        let carried_challenges = prepared
            .recursions
            .iter()
            .zip(prepared.dummy_slots)
            .filter(|(_, dummy)| !dummy)
            .map(|(recursion, _)| recursion.chals.clone())
            .collect();
        let dummy_accumulator = crate::dummy::pasta_dummy_wrap_sg();
        let physical_accumulators = prepared
            .proofs
            .iter()
            .zip(prepared.dummy_slots)
            .map(|(proof, dummy)| {
                if dummy {
                    (dummy_accumulator.x, dummy_accumulator.y)
                } else {
                    proof.sg
                }
            })
            .collect();
        let physical_challenges = prepared
            .recursions
            .iter()
            .map(|recursion| recursion.chals.clone())
            .collect();

        let app = RecordedApp {
            circuit: branch.circuit.clone(),
        };
        let main: crate::recursive_step::EmbeddedAppMain =
            std::sync::Arc::new(move |sys, previous_app_state| {
                app.main_with_previous_app_state(sys, Some(&witness), previous_app_state)
            });
        let indexes = self.step_indexes[branch_index]
            .take()
            .expect("compiled program Step indexes");
        prove_stage!("step prepared");
        if debug_stage == Some(30) {
            // Witness-synthesis-only probe of the step (no kimchi prove).
            self.step_indexes[branch_index] = Some(indexes);
            let t = snarky::wasm_instant::Instant::now();
            let log2 = crate::recursive_step::domain_log2_prepared_recursive_step_width2_arity::<
                RECORDED_N1_STEP_ROUNDS,
                RECORDED_BASE_WRAP_ROUNDS,
                RECORDED_N1_STEP_STMT_LEN,
                STEP_PI,
                ACTIVE,
            >(&prepared, Some(main));
            return Err(RecordedProveError::Program(format!(
                "DEBUG-STAGE 30 OK — witness synthesis {:.2?} -> 2^{log2} | {}",
                t.elapsed(),
                stage_timings.join(" | ")
            )));
        }
        let prepared = if debug_stage == Some(31) {
            // All-dummy recursion mask: same circuit, same stored index, no
            // kept previous challenge — isolates kimchi's kept-challenge
            // path (the proof itself is meaningless).
            let mut prepared = prepared;
            prepared.dummy_slots = [true, true];
            prepared
        } else {
            prepared
        };
        let (step, indexes) = crate::recursive_step::prove_prepared_recursive_step_width2_arity(
            prepared,
            Some(main),
            Some(indexes),
        );
        self.step_indexes[branch_index] = Some(indexes);
        prove_stage!("step proved");
        if debug_stage == Some(31) {
            return Err(RecordedProveError::Program(format!(
                "DEBUG-STAGE 31 OK — {}",
                stage_timings.join(" | ")
            )));
        }

        let real_unfinalized = previous_cycles
            .iter()
            .map(|(_, cycle)| {
                crate::recursive_step::program_unfinalized_from_previous(&cycle.step, &cycle.wrap)
            })
            .collect();
        let mut prepared_wrap = crate::recursive_step::prepare_program_recursive_wrap::<
            RECORDED_N1_STEP_ROUNDS,
            RECORDED_BASE_WRAP_ROUNDS,
            RECORDED_N1_STEP_STMT_LEN,
            STEP_PI,
            RECORDED_N2_STEP_ROUNDS,
            RECORDED_N2_WRAP_STMT_LEN,
            ACTIVE,
        >(
            &step,
            real_unfinalized,
            &recorded_slot_local_max(&self.branches, ACTIVE),
        );
        prepared_wrap.data.which_branch = branch_index;
        prepared_wrap.data.branches = self.wrap_branches.clone();
        prepared_wrap.data.step_statement_lagranges = self.wrap_statement_lagranges.clone();
        prove_stage!("wrap prepared");
        prepared_wrap.domain_log2 = 0; // natural wrap domain (jsoo Wrap_domains fixpoint)
        let prepared_wrap = crate::recursive_step::align_program_recursive_wrap_finalize_index(
            prepared_wrap,
            &self
                .wrap_indexes
                .as_ref()
                .expect("compiled program Wrap indexes")
                .1
                .index,
        );
        let indexes = self
            .wrap_indexes
            .take()
            .expect("compiled program Wrap indexes");
        let (wrap, indexes) =
            crate::recursive_step::prove_prepared_recursive_wrap(prepared_wrap, Some(indexes));
        self.wrap_indexes = Some(indexes);
        let proof = wrap
            .to_mina_network_proof(step.verifier.index.domain.log_size_of_group as u8)
            .map_err(RecordedProveError::RecursiveBackend)?;
        Ok(RecordedProofHandle {
            app_state,
            proof,
            inner: RecordedProgramCycleShaped {
                step,
                wrap,
                carried_accumulators,
                carried_challenges,
                physical_accumulators,
                physical_challenges,
                proofs_verified: branch.proofs_verified,
            }
            .into_inner(),
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

    /// The Mina transaction authorization proof: base64 of the OCaml
    /// `Pickles.Side_loaded.Proof.to_base64` S-expression, i.e. the string
    /// that goes in an account update's `authorization.proof`. Only base-case
    /// (N0) proofs are supported for now.
    pub fn to_transaction_base64(&self) -> Result<String, RecordedProveError> {
        match &self.inner {
            RecordedProofInner::R16(base) => Ok(base
                .to_mina_stable_v3()
                .map_err(RecordedProveError::Backend)?
                .to_transaction_base64()),
            _ => Err(RecordedProveError::UnsupportedStepRounds(0)),
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

    pub fn program_verification_messages(
        &self,
    ) -> Option<(Vec<(Fp, Fp)>, Vec<Vec<Fp>>, Vec<(Fp, Fp)>)> {
        match &self.inner {
            RecordedProofInner::Program(cycle) => Some((
                cycle.carried_accumulators.clone(),
                cycle.carried_challenges.clone(),
                cycle.step.messages_for_next_step_vk_pts.clone(),
            )),
            RecordedProofInner::ProgramW1(cycle) => Some((
                cycle.carried_accumulators.clone(),
                cycle.carried_challenges.clone(),
                cycle.step.messages_for_next_step_vk_pts.clone(),
            )),
            _ => None,
        }
    }
}

type RecordedRecursiveCycle = crate::recursive_step::RecursiveCycleProof<
    RECORDED_N1_STEP_ROUNDS,
    RECORDED_BASE_WRAP_ROUNDS,
    RECORDED_N1_STEP_ROUNDS,
    RECORDED_N1_STEP_STMT_LEN,
    RECORDED_N1_WRAP_STMT_LEN,
>;

#[allow(dead_code)]
struct RecordedProgramCycleShaped<const STEP_PI: usize, const ACTIVE: usize> {
    step: crate::recursive_step::RecursiveStepWidth2Proof<
        RECORDED_N1_STEP_ROUNDS,
        RECORDED_BASE_WRAP_ROUNDS,
        RECORDED_N1_STEP_STMT_LEN,
        STEP_PI,
        ACTIVE,
    >,
    wrap: crate::recursive_step::RecursiveWrapProof<
        RECORDED_N2_STEP_ROUNDS,
        RECORDED_N2_WRAP_STMT_LEN,
    >,
    carried_accumulators: Vec<(Fp, Fp)>,
    carried_challenges: Vec<Vec<Fp>>,
    physical_accumulators: Vec<(Fp, Fp)>,
    physical_challenges: Vec<Vec<Fp>>,
    proofs_verified: u8,
}

/// Maps a program cycle shape onto its [`RecordedProofInner`] variant, so the
/// shape-generic prove paths can store and recover previous proofs. Only the
/// two compiled shapes implement it.
trait ProgramCycleSlot: Sized {
    fn into_inner(self) -> RecordedProofInner;
    fn from_inner(inner: &RecordedProofInner) -> Option<&Self>;
}

impl ProgramCycleSlot for RecordedProgramCycleShaped<RECORDED_N2_STEP_STMT_LEN, 2> {
    fn into_inner(self) -> RecordedProofInner {
        RecordedProofInner::Program(self)
    }
    fn from_inner(inner: &RecordedProofInner) -> Option<&Self> {
        match inner {
            RecordedProofInner::Program(cycle) => Some(cycle),
            _ => None,
        }
    }
}

impl ProgramCycleSlot for RecordedProgramCycleShaped<RECORDED_N1_STEP_STMT_LEN, 1> {
    fn into_inner(self) -> RecordedProofInner {
        RecordedProofInner::ProgramW1(self)
    }
    fn from_inner(inner: &RecordedProofInner) -> Option<&Self> {
        match inner {
            RecordedProofInner::ProgramW1(cycle) => Some(cycle),
            _ => None,
        }
    }
}

enum RecordedProofInner {
    /// Proofs are always made over the full Tick SRS: 16 IPA rounds,
    /// 40-slot OCaml wrap statement.
    R16(crate::api::BaseCaseProof<RecordedApp, 16, 40>),
    Recursive(RecordedRecursiveCycle),
    Program(RecordedProgramCycleShaped<RECORDED_N2_STEP_STMT_LEN, 2>),
    ProgramW1(RecordedProgramCycleShaped<RECORDED_N1_STEP_STMT_LEN, 1>),
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
            RecordedProofInner::Program(_) | RecordedProofInner::ProgramW1(_) => {
                Err(RecordedProveError::Program(
                    "program proofs must be extended by their compiled program".into(),
                ))
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
        std::sync::Arc::new(move |sys, _previous_app_state| app.main(sys, Some(&witness)));
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
        std::sync::Arc::new(move |sys, _previous_app_state| app.main(sys, Some(&witness)));
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
/// Compiles a shared-wrap program and dumps every branch step circuit and
/// the shared wrap circuit in the `{ public_input_size, gates }` JSON schema
/// used by the jsoo parity harnesses.
#[doc(hidden)]
pub fn dump_recorded_program_circuits(
    branches: Vec<RecordedProgramBranch>,
) -> Result<String, RecordedProveError> {
    #[derive(serde::Serialize)]
    struct StepCircuitDump {
        public_input_size: usize,
        gates: Vec<kimchi::circuits::gate::CircuitGate<Fp>>,
        labels: Vec<String>,
    }
    #[derive(serde::Serialize)]
    struct WrapCircuitDump {
        public_input_size: usize,
        gates: Vec<kimchi::circuits::gate::CircuitGate<mina_curves::pasta::Fq>>,
        labels: Vec<String>,
    }
    #[derive(serde::Serialize)]
    struct ProgramDump {
        steps: Vec<StepCircuitDump>,
        wrap: WrapCircuitDump,
    }
    fn dump_shaped<const STEP_PI: usize, const ACTIVE: usize>(
        program: &RecordedCompiledProgramShaped<STEP_PI, ACTIVE>,
    ) -> ProgramDump {
        let steps = program
            .step_indexes
            .iter()
            .map(|indexes| {
                let prover = &indexes.as_ref().expect("compiled branch step").0;
                StepCircuitDump {
                    public_input_size: prover.index.cs.public,
                    gates: prover.index.cs.gates.to_vec(),
                    labels: prover.gate_labels().to_vec(),
                }
            })
            .collect();
        let wrap_prover = &program.wrap_indexes.as_ref().expect("compiled wrap").0;
        ProgramDump {
            steps,
            wrap: WrapCircuitDump {
                public_input_size: wrap_prover.index.cs.public,
                gates: wrap_prover.index.cs.gates.to_vec(),
                labels: wrap_prover.gate_labels().to_vec(),
            },
        }
    }
    let program = RecordedCompiledProgram::compile(branches)?;
    let dump = match &program {
        RecordedCompiledProgram::W2(p) => dump_shaped(p),
        RecordedCompiledProgram::W1(p) => dump_shaped(p),
    };
    serde_json::to_string(&dump)
        .map_err(|err| RecordedProveError::Program(format!("dump encoding failed: {err}")))
}

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

#[cfg(test)]
mod wrap_wdata_independence_tests {
    use super::*;
    use mina_curves::pasta::Fq;

    /// Probe: the wrap index compiled with the BOOTSTRAP wdata (generator
    /// points, zero scalars — `CompiledBaseCase::compile`) must be identical
    /// to the one compiled with the REAL wdata
    /// (`prove_base_case_with_wrap_dump`). The side-loaded VK parity harness
    /// shows sigma[0]/sigma[6] diverging between those two paths.
    #[test]
    fn wrap_index_is_wdata_value_independent() {
        let circuit = RecordedCircuit {
            previous_proof_widths: vec![],
            aux_count: 2,
            output: vec![LinComb::var(1)],
            constraints: vec![RecordedConstraint::Square {
                v: LinComb::var(0),
                square: LinComb::var(1),
            }],
            previous_state_slots: vec![],
        };
        let witness = vec![Fp::from(6u64), Fp::from(36u64)];
        let app = RecordedApp {
            circuit: circuit.clone(),
        };

        // Path A: compile with the bootstrap wdata; grab its wrap gates.
        let compiled = RecordedCompiledBase::compile(circuit, witness.clone()).expect("compile");
        let a_gates: Vec<kimchi::circuits::gate::CircuitGate<Fq>> = compiled
            .compiled
            .wrap_indexes
            .as_ref()
            .expect("wrap indexes")
            .0
            .index
            .cs
            .gates
            .to_vec();
        let actual_points = crate::api::wrap_verification_key_points(
            &compiled.compiled.wrap_indexes.as_ref().unwrap().1,
        );

        // Path B: full dump path — wrap compiled fresh with the REAL wdata.
        let (_, dump) = crate::api::prove_base_case_with_wrap_dump::<RecordedApp, 16, 40>(
            app,
            witness,
            actual_points,
        );

        assert_eq!(a_gates.len(), dump.gates.len(), "gate count");
        let mut diverging = vec![];
        for (i, (a, b)) in a_gates.iter().zip(&dump.gates).enumerate() {
            let typ = a.typ != b.typ;
            let coeffs = a.coeffs != b.coeffs;
            let wires = a.wires != b.wires;
            if typ || coeffs || wires {
                diverging.push((i, typ, coeffs, wires));
            }
        }
        for &(i, typ, coeffs, wires) in diverging.iter().take(30) {
            eprintln!(
                "row {i}: typ={typ} coeffs={coeffs} wires={wires}\n  A wires: {:?}\n  B wires: {:?}",
                a_gates[i].wires, dump.gates[i].wires
            );
        }
        assert!(
            diverging.is_empty(),
            "{} rows diverge between bootstrap-wdata and real-wdata wrap indexes",
            diverging.len()
        );
    }
}
