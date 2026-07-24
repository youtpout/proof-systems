//! The base-case (width 0) pickles API: wrap an application circuit into a
//! step proof and produce the wrap proof — the pickles proof — in one call.
//!
//! ```text
//! let (proof, statement) = prove_base_case(&app, witness, wrap_vk)?;
//! ```
//!
//! The pipeline is the one validated end-to-end in `tests/e2e.rs`:
//! step proof on Vesta (public input = the accumulator digest), transcript
//! witness via [`crate::wrap::wrap_witness`], statement packing via
//! [`crate::composition_types::wrap::wrap_statement_to_field_elements`], and
//! the wrap proof on Pallas running [`crate::wrap_main::wrap_main`] with the
//! bulletproof equation asserted.
//!
//! Recursion (width ≥ 1) adds `verify_one`/`step_main` on the step side and
//! the finalize loop on the wrap side — the circuit pieces exist; the
//! surrounding data plumbing lands with the recursive API.

use ark_ff::{BigInteger, Field, One, PrimeField};
use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine as _};
use kimchi::{
    circuits::wires::{COLUMNS, PERMUTS},
    curve::KimchiCurve,
};
use mina_curves::pasta::{Fp, Fq, Pallas, Vesta, VestaParameters};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi,
    sponge::{DefaultFqSponge, DefaultFrSponge},
};
use poly_commitment::{commitment::PolyComm, ipa::OpeningProof as IpaProof, SRS};
use serde::{Deserialize, Serialize};
use snarky::{api::SnarkyCircuit, loc, Boolean, FieldVar, RunState, SnarkyResult, SnarkyType};

use crate::{
    common::FULL_ROUNDS,
    composition_types::{plonk, BranchData, BulletproofChallenge, Features, ProofsVerified},
    finalize::{FinalizeParams, ShiftKind},
    incrementally_verify::{Advice, Messages, OpeningProof, VerificationKeyComm},
    inductive_rule::{CompiledRuleBackend, InductiveRule, RuleId},
    plonk_curve_ops::ShiftedScalar,
    scalar_challenge::ScalarChallenge,
    side_loaded::{SideLoadedKeyWitness, SideLoadedVerificationKey},
    step_verifier::{Claimed, FinalizeEvals},
    wrap_main::{wrap_main, PerUnfinalized, StepStatementElement},
};

type VestaBase = DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type VestaScalar = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type PallasBase =
    DefaultFqSponge<mina_curves::pasta::PallasParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
type PallasScalar = DefaultFrSponge<Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
pub type WrapPolishToken = kimchi::circuits::expr::PolishToken<
    Fq,
    kimchi::circuits::berkeley_columns::Column,
    kimchi::circuits::berkeley_columns::BerkeleyChallengeTerm,
>;

/// An application circuit hosted by a base-case step proof.
pub trait StepApp {
    /// The private witness of one execution.
    type Witness;

    /// Runs the application logic in-circuit and returns the app state
    /// exposed through the accumulator digest.
    fn main(
        &self,
        sys: &mut RunState<Fp>,
        witness: Option<&Self::Witness>,
    ) -> SnarkyResult<Vec<FieldVar<Fp>>>;

    /// The out-of-circuit app state values for a witness (must match what
    /// [`StepApp::main`] computes — used by the prover to build the digest).
    fn state(&self, witness: &Self::Witness) -> Vec<Fp>;
}

/// The step circuit hosting an application: `main` plus the width-0 statement
/// (public input = the accumulator digest `hash(wrap_vk, app_state)`).
pub struct StepCircuit<A: StepApp> {
    pub app: A,
}

/// o1js' OCaml Pickles binding prepends a small set of dummy constraints to
/// every rule so that the optional EC selector columns are always present in
/// the proving key. VK parity requires the Rust step circuit to emit the same
/// selector shape before the user circuit.
pub(crate) fn o1js_dummy_constraints(sys: &mut RunState<Fp>) -> SnarkyResult<()> {
    use ark_ec::{AffineRepr, CurveGroup};
    use snarky::gadgets::curve::Point;

    let x: FieldVar<Fp> = sys.compute(loc!(), |_| Fp::from(3u64))?;
    let g = Pallas::generator().into_group().into_affine();
    let gx: FieldVar<Fp> = sys.compute(loc!(), move |_| g.x)?;
    let gy: FieldVar<Fp> = sys.compute(loc!(), move |_| g.y)?;
    let g = Point::new(gx, gy);
    g.assert_on_curve(sys, loc!(), Fp::from(0u64), Fp::from(5u64))?;

    let _ = crate::scalar_challenge::scalar_to_field_raw_with_bits(sys, loc!(), &x, 16)?;
    let _ = crate::plonk_curve_ops::scale_fast(sys, loc!(), &g, &x, 5)?;
    let _ = crate::scalar_challenge::endo(sys, loc!(), &g, &x, 4, crate::endo::tick::base())?;
    Ok(())
}

impl<A: StepApp> SnarkyCircuit for StepCircuit<A> {
    type Curve = Vesta;
    /// Mina step proofs always carry `MAX_PROOFS_VERIFIED` accumulators
    /// (dummies at the base case — `Wrap_hack.pad_accumulator`).
    const PREV_CHALLENGES: usize = crate::common::MAX_PROOFS_VERIFIED;
    type Proof = IpaProof<Self::Curve, FULL_ROUNDS>;
    /// (app witness, the wrap VK's 28 commitment coordinates)
    type PrivateInput = (A::Witness, Vec<(Fp, Fp)>);
    type PublicInput = FieldVar<Fp>;
    type PublicOutput = ();

    fn srs(size: usize) -> std::sync::Arc<poly_commitment::ipa::SRS<Vesta>> {
        crate::common::tick_srs(size)
    }

    fn circuit(
        &self,
        sys: &mut RunState<Fp>,
        digest: Self::PublicInput,
        private: Option<&Self::PrivateInput>,
    ) -> SnarkyResult<()> {
        use crate::{
            composition_types::PlonkVerificationKeyEvals,
            hash_messages::{hash_messages_for_next_step_proof, sponge_after_index},
        };
        use snarky::gadgets::curve::Point;

        o1js_dummy_constraints(sys)?;
        let app_state = self.app.main(sys, private.map(|p| &p.0))?;

        let mut pts = vec![];
        for i in 0..28 {
            let (px, py) = (
                sys.compute(loc!(), move |_| private.unwrap().1[i].0)?,
                sys.compute(loc!(), move |_| private.unwrap().1[i].1)?,
            );
            pts.push(Point::new(px, py));
        }
        // The wrap key crosses a trust boundary (it is only known at proving
        // time), so each commitment is constrained to the Pallas curve —
        // mirroring OCaml snarky_curve's `assert_on_curve` emitted by the
        // `exists Inner_curve.typ` in step_main: x² (square), x³ = x²·x
        // (r1cs), y² = x³ + b (square) with b = 5.
        for pt in &pts {
            let x = pt.x.clone();
            let y = pt.y.clone();
            let x2: FieldVar<Fp> = sys.compute(loc!(), {
                let x = x.clone();
                move |env| {
                    let v: Fp = env.read_var(&x);
                    v * v
                }
            })?;
            sys.add_constraint(
                snarky::runner::Constraint::BasicSnarkyConstraint(
                    snarky::constraint_system::BasicSnarkyConstraint::Square(x.clone(), x2.clone()),
                ),
                Some("vk point x^2".into()),
                loc!(),
            )?;
            let x3 = x2.mul(&x, Some("vk point x^3".into()), loc!(), sys)?;
            let rhs = x3 + FieldVar::Constant(Fp::from(5u64));
            sys.add_constraint(
                snarky::runner::Constraint::BasicSnarkyConstraint(
                    snarky::constraint_system::BasicSnarkyConstraint::Square(y, rhs),
                ),
                Some("vk point on curve".into()),
                loc!(),
            )?;
        }
        let mut it = pts.into_iter();
        let vk = PlonkVerificationKeyEvals {
            sigma_comm: (0..PERMUTS).map(|_| it.next().unwrap()).collect(),
            coefficients_comm: (0..15).map(|_| it.next().unwrap()).collect(),
            generic_comm: it.next().unwrap(),
            psm_comm: it.next().unwrap(),
            complete_add_comm: it.next().unwrap(),
            mul_comm: it.next().unwrap(),
            emul_comm: it.next().unwrap(),
            endomul_scalar_comm: it.next().unwrap(),
        };
        let after_index = sponge_after_index(sys, loc!(), &vk);
        let computed =
            hash_messages_for_next_step_proof(sys, loc!(), &after_index, &app_state, &[], &[])?;
        computed.assert_equals(sys, loc!(), &digest)?;
        Ok(())
    }
}

/// Application step circuit whose wrap VK is supplied at proving time and
/// validated in-circuit against one inductive rule.
pub struct SideLoadedStepCircuit<A: StepApp> {
    pub app: A,
    pub rule: InductiveRule,
}

impl<A: StepApp> SnarkyCircuit for SideLoadedStepCircuit<A> {
    type Curve = Vesta;
    type Proof = IpaProof<Self::Curve, FULL_ROUNDS>;
    type PrivateInput = (A::Witness, SideLoadedKeyWitness);
    type PublicInput = FieldVar<Fp>;
    type PublicOutput = ();

    fn circuit(
        &self,
        sys: &mut RunState<Fp>,
        digest: Self::PublicInput,
        private: Option<&Self::PrivateInput>,
    ) -> SnarkyResult<()> {
        use crate::{
            composition_types::PlonkVerificationKeyEvals,
            hash_messages::{hash_messages_for_next_step_proof, sponge_after_index},
        };
        use snarky::gadgets::curve::Point;

        o1js_dummy_constraints(sys)?;
        let app_state = self.app.main(sys, private.map(|input| &input.0))?;

        let step_domain: FieldVar<Fp> = sys.compute(loc!(), move |_| {
            Fp::from(u64::from(private.unwrap().1.step_domain_log2))
        })?;
        step_domain.assert_equals(
            sys,
            loc!(),
            &FieldVar::constant(Fp::from(u64::from(self.rule.step_domain_log2))),
        )?;
        let proofs_verified: FieldVar<Fp> = sys.compute(loc!(), move |_| {
            Fp::from(u64::from(private.unwrap().1.proofs_verified))
        })?;
        proofs_verified.assert_equals(
            sys,
            loc!(),
            &FieldVar::constant(Fp::from(self.rule.proofs_verified.to_usize() as u64)),
        )?;
        let expected_wrap_domain =
            crate::common::wrap_domain_log2(self.rule.proofs_verified.to_usize()) as u64;
        let wrap_domain: FieldVar<Fp> = sys.compute(loc!(), move |_| {
            Fp::from(u64::from(private.unwrap().1.wrap_domain_log2))
        })?;
        wrap_domain.assert_equals(
            sys,
            loc!(),
            &FieldVar::constant(Fp::from(expected_wrap_domain)),
        )?;

        let points = (0..crate::side_loaded::SideLoadedVerificationKey::COMMITMENT_COUNT)
            .map(|index| {
                let (x, y): (FieldVar<Fp>, FieldVar<Fp>) =
                    sys.compute(loc!(), move |_| private.unwrap().1.commitments[index])?;
                let point = Point::new(x, y);
                point.assert_on_curve(sys, loc!(), Fp::from(0u64), Fp::from(5u64))?;
                Ok(point)
            })
            .collect::<SnarkyResult<Vec<_>>>()?;
        let mut points = points.into_iter();
        let vk = PlonkVerificationKeyEvals {
            sigma_comm: (0..PERMUTS).map(|_| points.next().unwrap()).collect(),
            coefficients_comm: (0..COLUMNS).map(|_| points.next().unwrap()).collect(),
            generic_comm: points.next().unwrap(),
            psm_comm: points.next().unwrap(),
            complete_add_comm: points.next().unwrap(),
            mul_comm: points.next().unwrap(),
            emul_comm: points.next().unwrap(),
            endomul_scalar_comm: points.next().unwrap(),
        };
        let after_index = sponge_after_index(sys, loc!(), &vk);
        let computed =
            hash_messages_for_next_step_proof(sys, loc!(), &after_index, &app_state, &[], &[])?;
        computed.assert_equals(sys, loc!(), &digest)
    }
}

/// Everything the wrap circuit witnesses about the step proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WrapStepStatementSlot {
    Field(Fq),
    Packed { value: Fq, num_bits: usize },
    Bool(bool),
}

/// One previous proof-state carried by a recursive step statement and
/// finalized by the wrap circuit before it verifies the step proof.
#[derive(Clone)]
pub struct WrapUnfinalizedWitnessData {
    pub finalize_tokens: Vec<WrapPolishToken>,
    pub finalize_domain: ark_poly::Radix2EvaluationDomain<Fq>,
    pub finalize_srs_log2: u32,
    pub finalize_endo: Fq,
    pub finalize_endo_r: Fq,
    pub finalize_shifts: Vec<Fq>,
    pub ft_eval1: Fq,
    pub public_evals: [Vec<Fq>; 2],
    pub evals_flat: Vec<(Fq, Fq)>,
    pub alpha: Fq,
    pub beta: Fq,
    pub gamma: Fq,
    pub zeta: Fq,
    pub xi: Fq,
    pub cip_repr: Fq,
    pub b_repr: Fq,
    pub perm_repr: Fq,
    pub bulletproof_challenges: Vec<Fq>,
    pub sponge_digest_before_evaluations: Fq,
    pub should_finalize: bool,
    pub old_bulletproof_challenges: Vec<Vec<Fq>>,
    pub prev_step_acc: (Fq, Fq),
    pub hash_dummy_challenges: Vec<Vec<Fq>>,
    pub hash_old_bulletproof_challenges: Vec<Vec<Fq>>,
    /// How many LEADING `old_bulletproof_challenges` vectors are the
    /// protocol dummy pad, entered as circuit CONSTANTS
    /// (`Wrap_hack.Checked.pad_challenges`) rather than witnessed. Zero for
    /// width-2 programs and every legacy path.
    pub constant_pad_challenges: usize,
}

/// The optional-gate / lookup feature usage of a step branch, derived from its
/// verifier index. Mirrors `kimchi::circuits::constraints::FeatureFlags`, plus
/// the step VK's lookup commitments the wrap must absorb into the Fq transcript
/// (in the kimchi `VerifierIndex::digest` order) and combine into the polyscale.
/// `None` in [`WrapBranchData::lookup`] means the branch uses no optional gates,
/// so the wrap stays byte-identical to the pre-lookup layout.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LookupBranchData {
    pub range_check0: bool,
    pub range_check1: bool,
    pub foreign_field_add: bool,
    pub foreign_field_mul: bool,
    pub xor: bool,
    pub rot: bool,
    /// The o1js runtime/plain lookup pattern (kimchi `LookupPattern::Lookup`).
    pub lookup: bool,
    pub joint_lookup_used: bool,
    pub uses_runtime_tables: bool,
    /// Step VK `lookup_index.lookup_table` commitments (one per table chunk).
    pub lookup_table: Vec<(Fq, Fq)>,
    pub table_ids: Option<(Fq, Fq)>,
    pub runtime_tables_selector: Option<(Fq, Fq)>,
    /// `lookup_selectors` in kimchi `digest` order: xor, lookup, range_check, ffmul.
    pub selector_xor: Option<(Fq, Fq)>,
    pub selector_lookup: Option<(Fq, Fq)>,
    pub selector_range_check: Option<(Fq, Fq)>,
    pub selector_ffmul: Option<(Fq, Fq)>,
    /// Optional GATE selector commitments (distinct from the lookup selectors),
    /// absorbed into the index digest BEFORE the lookup commitments in kimchi
    /// `digest` order: range_check0, range_check1, ffmul, ffadd, xor, rot.
    pub gate_range_check0: Option<(Fq, Fq)>,
    pub gate_range_check1: Option<(Fq, Fq)>,
    pub gate_foreign_field_mul: Option<(Fq, Fq)>,
    pub gate_foreign_field_add: Option<(Fq, Fq)>,
    pub gate_xor: Option<(Fq, Fq)>,
    pub gate_rot: Option<(Fq, Fq)>,
}

/// The proof lookup commitments (`sorted[]`, `aggreg`, optional `runtime`) a
/// wrap witness carries. For structure-only VK compiles the VALUES are
/// irrelevant, so a lookup-using branch gets on-curve placeholders sized by
/// `sorted_count`; a no-lookup branch gets empty vectors.
pub(crate) fn proof_lookup_commitments(
    lk: &Option<LookupBranchData>,
) -> (Vec<(Fq, Fq)>, (Fq, Fq), Option<(Fq, Fq)>) {
    match lk {
        Some(l) => {
            use ark_ec::AffineRepr;
            let g = Vesta::generator();
            let pt = (g.x, g.y);
            let runtime = if l.uses_runtime_tables { Some(pt) } else { None };
            (vec![pt; l.sorted_count()], pt, runtime)
        }
        None => (vec![], (Fq::from(0u64), Fq::from(0u64)), None),
    }
}

fn plonk_features_from_lookup(lookup: &Option<LookupBranchData>) -> Features<bool> {
    match lookup {
        None => Features::none(),
        Some(l) => Features {
            range_check0: l.range_check0,
            range_check1: l.range_check1,
            foreign_field_add: l.foreign_field_add,
            foreign_field_mul: l.foreign_field_mul,
            xor: l.xor,
            rot: l.rot,
            lookup: l.lookup,
            runtime_tables: l.uses_runtime_tables,
        },
    }
}

impl LookupBranchData {
    /// Number of `sorted` lookup polynomials in the proof = kimchi's
    /// `max_lookups_per_row + 1` over the used patterns (Xor/RangeCheck/
    /// ForeignFieldMul = 4, Lookup = 3).
    pub fn sorted_count(&self) -> usize {
        let mut max = 0usize;
        if self.xor {
            max = max.max(4);
        }
        if self.range_check0 || self.range_check1 || self.rot {
            max = max.max(4);
        }
        if self.foreign_field_mul {
            max = max.max(4);
        }
        if self.lookup {
            max = max.max(3);
        }
        max + 1
    }

    /// Extracts the optional-gate / lookup usage of a step branch from its
    /// verifier index, or `None` if the branch uses no lookup gates.
    pub fn from_step_verifier(
        index: &kimchi::verifier_index::VerifierIndex<
            FULL_ROUNDS,
            Vesta,
            poly_commitment::ipa::SRS<Vesta>,
        >,
    ) -> Option<Self> {
        let point = |c: &poly_commitment::commitment::PolyComm<Vesta>| {
            let p = c.chunks[0];
            (p.x, p.y)
        };
        let opt = |c: &Option<poly_commitment::commitment::PolyComm<Vesta>>| c.as_ref().map(point);
        index.lookup_index.as_ref().map(|li| {
            let sel = &li.lookup_selectors;
            LookupBranchData {
                range_check0: index.range_check0_comm.is_some(),
                range_check1: index.range_check1_comm.is_some(),
                foreign_field_add: index.foreign_field_add_comm.is_some(),
                foreign_field_mul: index.foreign_field_mul_comm.is_some(),
                xor: index.xor_comm.is_some(),
                rot: index.rot_comm.is_some(),
                lookup: sel.lookup.is_some(),
                joint_lookup_used: li.joint_lookup_used,
                uses_runtime_tables: li.runtime_tables_selector.is_some(),
                lookup_table: li.lookup_table.iter().map(point).collect(),
                table_ids: opt(&li.table_ids),
                runtime_tables_selector: opt(&li.runtime_tables_selector),
                selector_xor: opt(&sel.xor),
                selector_lookup: opt(&sel.lookup),
                selector_range_check: opt(&sel.range_check),
                selector_ffmul: opt(&sel.ffmul),
                gate_range_check0: opt(&index.range_check0_comm),
                gate_range_check1: opt(&index.range_check1_comm),
                gate_foreign_field_mul: opt(&index.foreign_field_mul_comm),
                gate_foreign_field_add: opt(&index.foreign_field_add_comm),
                gate_xor: opt(&index.xor_comm),
                gate_rot: opt(&index.rot_comm),
            }
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WrapBranchData {
    pub proofs_verified: usize,
    pub step_domain_log2: u8,
    pub generic: (Fq, Fq),
    pub psm: (Fq, Fq),
    pub complete_add: (Fq, Fq),
    pub mul: (Fq, Fq),
    pub emul: (Fq, Fq),
    pub endomul_scalar: (Fq, Fq),
    pub coefficients: Vec<(Fq, Fq)>,
    pub sigma_init: Vec<(Fq, Fq)>,
    pub sigma_last: Vec<(Fq, Fq)>,
    /// Optional-gate / lookup usage; `None` for the common no-lookup branch.
    pub lookup: Option<LookupBranchData>,
}

impl WrapBranchData {
    pub fn from_step_verifier(
        index: &kimchi::verifier_index::VerifierIndex<
            FULL_ROUNDS,
            Vesta,
            poly_commitment::ipa::SRS<Vesta>,
        >,
        proofs_verified: usize,
    ) -> Self {
        let point = |commitment: &poly_commitment::commitment::PolyComm<Vesta>| {
            let point = commitment.chunks[0];
            (point.x, point.y)
        };
        let lookup = LookupBranchData::from_step_verifier(index);
        Self {
            proofs_verified,
            step_domain_log2: index.domain.log_size_of_group as u8,
            generic: point(&index.generic_comm),
            psm: point(&index.psm_comm),
            complete_add: point(&index.complete_add_comm),
            mul: point(&index.mul_comm),
            emul: point(&index.emul_comm),
            endomul_scalar: point(&index.endomul_scalar_comm),
            coefficients: index.coefficients_comm.iter().map(point).collect(),
            sigma_init: index.sigma_comm[..PERMUTS - 1].iter().map(point).collect(),
            sigma_last: vec![point(&index.sigma_comm[PERMUTS - 1])],
            lookup,
        }
    }
}

#[derive(Clone)]
pub struct WrapWitnessData {
    /// Branch selected by the step proof being wrapped. A one-branch circuit
    /// keeps the historical branch-zero layout byte-for-byte; a program Wrap
    /// supplies every branch here and selects one with a checked one-hot.
    pub which_branch: usize,
    pub branches: Vec<WrapBranchData>,
    pub step_domain_log2: u8,
    pub step_vk_digest: Fq,
    /// Optional-gate / lookup usage of the (single) step branch being wrapped;
    /// `None` for the common no-lookup case. For multi-branch programs the
    /// per-branch data lives in `branches`.
    pub lookup: Option<LookupBranchData>,
    /// Proof lookup commitments (single chunk each): the `sorted` polynomials,
    /// the `aggreg` polynomial, and the optional `runtime` table. Empty when the
    /// step used no lookup gates.
    pub lookup_sorted: Vec<(Fq, Fq)>,
    pub lookup_aggreg: (Fq, Fq),
    pub lookup_runtime: Option<(Fq, Fq)>,
    pub generic: (Fq, Fq),
    pub psm: (Fq, Fq),
    pub complete_add: (Fq, Fq),
    pub mul: (Fq, Fq),
    pub emul: (Fq, Fq),
    pub endomul_scalar: (Fq, Fq),
    pub coefficients: Vec<(Fq, Fq)>,
    pub sigma_init: Vec<(Fq, Fq)>,
    pub sigma_last: Vec<(Fq, Fq)>,
    pub w_comm: Vec<(Fq, Fq)>,
    pub z_comm: (Fq, Fq),
    pub t_comm: Vec<(Fq, Fq)>,
    pub lr: Vec<((Fq, Fq), (Fq, Fq))>,
    pub delta: (Fq, Fq),
    pub sg: (Fq, Fq),
    pub z1_repr: Fq,
    pub z2_repr: Fq,
    /// Physical recursion accumulators folded by the Kimchi step proof.
    /// This is padded independently of the logical `unfinalized` entries.
    pub sg_olds: Vec<(Fq, Fq)>,
    pub unfinalized: Vec<WrapUnfinalizedWitnessData>,
    pub step_statement: Vec<WrapStepStatementSlot>,
    /// The x_hat (Lagrange, correction) constant pairs per expanded step
    /// statement element, PER BRANCH (outer index). Branches whose step
    /// domains all agree collapse to constants in-circuit (OCaml
    /// `lagrange_with_correction`'s all-equal shortcut); heterogeneous
    /// domains select via the which_branch one-hot.
    pub step_statement_lagranges: Vec<Vec<((Fq, Fq), (Fq, Fq))>>,
    pub h: (Fq, Fq),
    pub new_acc_dummies: Vec<Vec<Fq>>,
}

/// The base-case wrap circuit: [`wrap_main`] over one step proof, public
/// input = the wrap statement (13 scalars, `ROUNDS` bulletproof challenges,
/// branch data, 8 feature flags, optional joint combiner
/// (`STMT_LEN = 13 + ROUNDS + 11` — the OCaml 40-slot layout).
pub struct WrapCircuit<const ROUNDS: usize, const STMT_LEN: usize> {
    /// Compilation witness used only while building the constraint system.
    /// Proving supplies the current witness through `PrivateInput`, allowing
    /// the same prover index to be reused for multiple proofs.
    pub w: Option<WrapWitnessData>,
}

impl<const ROUNDS: usize, const STMT_LEN: usize> SnarkyCircuit for WrapCircuit<ROUNDS, STMT_LEN> {
    type Curve = Pallas;
    const PREV_CHALLENGES: usize = crate::common::MAX_PROOFS_VERIFIED;
    type Proof = IpaProof<Self::Curve, FULL_ROUNDS>;
    type PrivateInput = WrapWitnessData;
    type PublicInput = [FieldVar<Fq>; STMT_LEN];
    type PublicOutput = ();

    fn srs(size: usize) -> std::sync::Arc<poly_commitment::ipa::SRS<Pallas>> {
        crate::common::tock_srs(size)
    }

    fn circuit(
        &self,
        sys: &mut RunState<Fq>,
        stmt: Self::PublicInput,
        private: Option<&Self::PrivateInput>,
    ) -> SnarkyResult<()> {
        use groupmap::GroupMap;
        use snarky::gadgets::curve::Point;

        // OCaml's backend never flushes a pending generic half before a custom
        // gate — it stays queued (across arbitrarily many custom rows) until
        // the next half arrives (plonk_constraint_system.ml:1453) or
        // finalization. E.g. each bulletproof round's φ·x seal pairs with the
        // next round's on-curve half across ~70 custom rows in the jsoo dump.

        let w = private
            .or(self.w.as_ref())
            .expect("WrapCircuit needs a compilation or proving witness");
        // Every witnessed point goes through OCaml's `exists Inner_curve.typ`,
        // whose check is `assert_on_curve` (Vesta: y² = x³ + 5).
        let mkpt = |sys: &mut RunState<Fq>, p: (Fq, Fq)| -> SnarkyResult<Point<Fq>> {
            let point = Point::new(
                sys.compute(loc!(), move |_| p.0)?,
                sys.compute(loc!(), move |_| p.1)?,
            );
            point.assert_on_curve(sys, loc!(), Fq::from(0u64), Fq::from(5u64))?;
            Ok(point)
        };
        // OCaml's `exists Bulletproof.wrap_typ` (wrap_main.ml:440) witnesses
        // every opening point through `Inner_curve.typ`, whose check emits an
        // on-curve assert — the jsoo dump's 32 pre-sponge c=5 markers wired to
        // the bulletproof zone are exactly lr (15×2), delta and sg.
        let mkpts = |sys: &mut RunState<Fq>, ps: &[(Fq, Fq)]| -> SnarkyResult<Vec<Point<Fq>>> {
            let mut out = vec![];
            // `Vector.wrap_typ Inner_curve.typ` witnesses the tail first.
            // Preserve the logical vector after matching that emission order.
            for &p in ps.iter().rev() {
                out.push(mkpt(sys, p)?);
            }
            out.reverse();
            Ok(out)
        };
        let w1 = |sys: &mut RunState<Fq>, v: Fq| sys.compute(loc!(), move |_| v);
        let wvec = |sys: &mut RunState<Fq>, vs: &[Fq]| -> SnarkyResult<Vec<FieldVar<Fq>>> {
            let mut out = vec![];
            for &v in vs {
                out.push(w1(sys, v)?);
            }
            Ok(out)
        };
        let cpt = |p: (Fq, Fq)| Point::new(FieldVar::constant(p.0), FieldVar::constant(p.1));
        let other_field_equal = |sys: &mut RunState<Fq>,
                                 lhs: &FieldVar<Fq>,
                                 rhs: Fq,
                                 reverse: bool|
         -> SnarkyResult<Boolean<Fq>> {
            let rhs = FieldVar::constant(rhs);
            let z = if reverse { &rhs - lhs } else { lhs - &rhs };
            let z_for_witness = z.clone();
            let (result, z_inv): (FieldVar<Fq>, FieldVar<Fq>) =
                sys.compute(loc!(), move |env| {
                    let z = env.read_var(&z_for_witness);
                    match z.inverse() {
                        Some(inv) => (Fq::from(0u64), inv),
                        None => (Fq::one(), Fq::from(0u64)),
                    }
                })?;
            // `Checked.assert_all` stores this pair in reverse order.
            sys.assert_r1cs(
                Some("equals_2".into()),
                loc!(),
                result.clone(),
                z.clone(),
                FieldVar::zero(),
            )?;
            sys.assert_r1cs(
                Some("equals_1".into()),
                loc!(),
                z_inv,
                z,
                FieldVar::constant(Fq::one()) - &result,
            )?;
            Ok(Boolean::create_unsafe(result))
        };
        // destructure the statement (to_data order)
        let cip = stmt[0].clone();
        let b = stmt[1].clone();
        let zsl = stmt[2].clone();
        let zds = stmt[3].clone();
        let perm = stmt[4].clone();
        let beta = stmt[5].clone();
        let gamma = stmt[6].clone();
        let alpha = stmt[7].clone();
        let zeta = stmt[8].clone();
        let xi = stmt[9].clone();
        let sponge_digest = stmt[10].clone();
        let msgs_wrap_digest = stmt[11].clone();
        let bp: Vec<FieldVar<Fq>> = stmt[13..13 + ROUNDS].to_vec();
        let branch_data = stmt[13 + ROUNDS].clone();
        // OCaml statement `Typ.check` boolean-constrains each `Maybe` feature
        // flag (and the joint_combiner / uses_lookups `Opt` flag) at witness
        // time — the VERY FIRST wrap constraints, BEFORE the Other_field
        // forbidden checks (verified via the jsoo gate-label/constraint dump:
        // constraints 0,1 = `Boolean(Var 34=xor)`, `Boolean(Var 38=jc)` for the
        // mixed case). A feature is `Maybe` iff some-but-not-all branches use
        // it; `Yes`/`No` (all/none) fold to constants (`constant_layout_typ`
        // No|Yes emits no check, opt.ml:125) so alllookup/nolookup stay
        // byte-identical. rust's fixed `[FieldVar; STMT_LEN]` public input reads
        // these slots via `create_unsafe` (no check), so emit the missing
        // booleans here to align the whole circuit (this is the +1 that was
        // propagating through the entire mixed wrap).
        {
            let per_branch: Vec<Option<&LookupBranchData>> = if w.branches.is_empty() {
                vec![w.lookup.as_ref()]
            } else {
                w.branches.iter().map(|b| b.lookup.as_ref()).collect()
            };
            let feat_base = stmt.len() - 10;
            let is_maybe = |get: &dyn Fn(&LookupBranchData) -> bool| -> bool {
                let mut any = false;
                let mut all = true;
                for o in &per_branch {
                    let u = o.map(|l| get(l)).unwrap_or(false);
                    any |= u;
                    all &= u;
                }
                any && !all
            };
            // Feature flags in `Plonk_types.Features.to_data` order, then the
            // joint_combiner / uses_lookups Opt flag (stmt slot 8 = stmt[38]).
            let flags: [(bool, usize); 8] = [
                (is_maybe(&|l| l.range_check0), 0),
                (is_maybe(&|l| l.range_check1), 1),
                (is_maybe(&|l| l.foreign_field_add), 2),
                (is_maybe(&|l| l.foreign_field_mul), 3),
                (is_maybe(&|l| l.xor), 4),
                (is_maybe(&|l| l.rot), 5),
                (is_maybe(&|l| l.lookup), 6),
                (is_maybe(&|l| l.uses_runtime_tables), 7),
            ];
            for (m, slot) in flags {
                if m {
                    Boolean::create_unsafe(stmt[feat_base + slot].clone()).check(sys, loc!())?;
                }
            }
            // uses_lookups Opt flag: Maybe iff some-but-not-all branches use any
            // lookup at all (i.e. carry LookupBranchData).
            let present_any = per_branch.iter().any(|o| o.is_some());
            let present_all = per_branch.iter().all(|o| o.is_some());
            if present_any && !present_all {
                Boolean::create_unsafe(stmt[feat_base + 8].clone()).check(sys, loc!())?;
            }
        }
        // OCaml `Wrap.Other_field.check`: each deferred Tick-field slot of the
        // statement (cip, b, zeta_to_srs_length, zeta_to_domain_size, perm)
        // must not be one of the forbidden shifted values — the 255-bit
        // patterns whose Type1 decoding is ambiguous modulo the Tick modulus.
        // This runs during the statement's `exists` in OCaml, i.e. BEFORE the
        // which_branch / branch_data logic of the circuit body.
        {
            let forbidden = crate::shifted_value::forbidden_shifted_values_fq();
            // OCaml applies `Other_field.check` to the fq slots in REVERSE
            // order (perm, zds, zsl, b, cip) — the spec/typ processes the
            // `[cip; b; zsl; zds; perm]` vector back-to-front. Match that so
            // the per-slot forbidden blocks land on the same rows/wiring.
            for slot in stmt[0..5].iter().rev() {
                let mut eqs = Vec::with_capacity(forbidden.len());
                for &value in &forbidden {
                    eqs.push(other_field_equal(sys, slot, value, false)?);
                }
                let eq_refs: Vec<&snarky::Boolean<Fq>> = eqs.iter().collect();
                let any = snarky::Boolean::any(&eq_refs, sys, loc!())?;
                any.not().to_field_var().assert_equals(
                    sys,
                    loc!(),
                    &FieldVar::constant(Fq::from(1u64)),
                )?;
            }
        }
        // OCaml always witnesses `which_branch`, builds a one-hot vector, and
        // selects the branch width/domain through `Pseudo.choose`, even for a
        // single-branch o1js program.  Mirror that shape instead of folding the
        // branch data to a pure constant.
        let which_branch_value = w.which_branch;
        let which_branch: FieldVar<Fq> =
            sys.compute(loc!(), move |_| Fq::from(which_branch_value as u64))?;
        let branch_count = w.branches.len().max(1);
        // `One_hot_vector.of_index` is
        //   `Vector.init length ~f:(fun j -> Field.equal (Field.of_int j) i)`
        // and `Vector.init` (`vector.ml:124`) is `f i :: init (i + 1) n ~f`.
        // OCaml evaluates constructor arguments RIGHT-TO-LEFT, so the tail
        // recurses first and `f` actually runs for j = length-1 down to 0.
        // The bits are therefore CREATED — and their `equal` gadgets emitted —
        // in DESCENDING branch order, giving branch `length-1` the LOWEST
        // variable index. That ordering is structural: `reduce_lincom` sorts a
        // lincom's terms by ASCENDING VARIABLE INDEX, so the creation order
        // decides which branch weight lands in the `l` slot and which in `r`.
        let mut branches = Vec::with_capacity(branch_count);
        for index in (0..branch_count).rev() {
            branches.push(other_field_equal(
                sys,
                &which_branch,
                Fq::from(index as u64),
                true,
            )?);
        }
        // ...but the vector itself stays in ascending branch order.
        branches.reverse();
        let branch0 = branches[0].clone();
        // `One_hot_vector.of_index` finishes with `Boolean.Assert.any`.  Even
        // for a single branch Snarky implements that assertion as
        // `assert_non_zero(sum bits)`: witness the inverse and constrain
        // `inverse * branch0 = 1`.  A linear `branch0 = 1` is logically
        // equivalent, but does not emit OCaml's `Checked.inv` R1CS half and
        // shifts the first verifier-index Poseidon train by one Generic row.
        let branch_sum = branches
            .iter()
            .fold(FieldVar::zero(), |sum, branch| sum + branch.to_field_var());
        let branch_sum_for_witness = branch_sum.clone();
        let branch_sum_inv: FieldVar<Fq> = sys.compute(loc!(), move |env| {
            env.read_var(&branch_sum_for_witness)
                .inverse()
                .unwrap_or_else(|| Fq::from(0u64))
        })?;
        sys.assert_r1cs(
            Some("one-hot any".into()),
            loc!(),
            branch_sum.clone(),
            branch_sum_inv,
            FieldVar::constant(Fq::from(1u64)),
        )?;
        let branch_definitions = if w.branches.is_empty() {
            vec![WrapBranchData {
                proofs_verified: w
                    .unfinalized
                    .iter()
                    .filter(|entry| entry.should_finalize)
                    .count(),
                step_domain_log2: w.step_domain_log2,
                generic: w.generic,
                psm: w.psm,
                complete_add: w.complete_add,
                mul: w.mul,
                emul: w.emul,
                endomul_scalar: w.endomul_scalar,
                coefficients: w.coefficients.clone(),
                sigma_init: w.sigma_init.clone(),
                sigma_last: w.sigma_last.clone(),
                lookup: w.lookup.clone(),
            }]
        } else {
            w.branches.clone()
        };
        let proofs_verified = if branch_count == 1 {
            branch0.to_field_var().mul(
                &FieldVar::constant(Fq::from(branch_definitions[0].proofs_verified as u64)),
                Some("choose proofs_verified".into()),
                loc!(),
                sys,
            )?
        } else {
            branches.iter().zip(&branch_definitions).fold(
                FieldVar::zero(),
                |sum, (branch, definition)| {
                    sum + branch
                        .to_field_var()
                        .scale(Fq::from(definition.proofs_verified as u64))
                },
            )
        };
        // `actual_proofs_verified_mask = Wrap_verifier.mask (which_branch,
        // step_widths)` (wrap_main.ml:165): `Util.ones_vector` with
        // `first_zero = Pseudo.choose(which_branch, step_widths)` — emitted
        // right here, before `domain_log2`, as in OCaml.
        let actual_proofs_verified_mask: Vec<Boolean<Fq>> = {
            let mut mask = Vec::with_capacity(w.sg_olds.len());
            let mut keep = Boolean::true_();
            for i in 0..w.sg_olds.len() {
                let is_first_zero =
                    proofs_verified.equal(sys, loc!(), &FieldVar::constant(Fq::from(i as u64)))?;
                keep = keep.and(&is_first_zero.not(), sys, loc!());
                mask.push(keep.clone());
            }
            mask
        };
        let domain_log2 = if branch_count == 1 {
            branch0.to_field_var().mul(
                &FieldVar::constant(Fq::from(u64::from(branch_definitions[0].step_domain_log2))),
                Some("choose domain_log2".into()),
                loc!(),
                sys,
            )?
        } else {
            branches.iter().zip(&branch_definitions).fold(
                FieldVar::zero(),
                |sum, (branch, definition)| {
                    sum + branch
                        .to_field_var()
                        .scale(Fq::from(u64::from(definition.step_domain_log2)))
                },
            )
        };
        // `Branch_data.Checked.Wrap.pack { proofs_verified_mask =
        // extend_front(rev(mask), 2, false); domain_log2 }` asserted against
        // the branch_data statement slot (wrap_main.ml:180-189). With the
        // reversed ones-vector, bit0 = mask[last] (pv≥2) and bit1 =
        // mask[first] (pv≥1) — N0 → 0, N1 → 2, N2 → 3.
        assert!(actual_proofs_verified_mask.len() <= 2, "max width two");
        let pad = 2 - actual_proofs_verified_mask.len();
        let mut expected_branch_data = domain_log2.scale(Fq::from(4u64));
        for (i, bit) in actual_proofs_verified_mask.iter().rev().enumerate() {
            expected_branch_data = &expected_branch_data
                + &bit.to_field_var().scale(Fq::from(1u64 << (pad + i)));
        }
        branch_data.assert_equals(sys, loc!(), &expected_branch_data)?;
        // OCaml `exists prev_proof_state` (wrap_main.ml:191, before
        // `choose_key`): the per-unfinalized DEFERRED VALUES — plonk
        // challenges, Type2 representatives, bulletproof challenges, sponge
        // digest and should_finalize — are witnessed here. The evals and old
        // bulletproof challenges come later (:306/:341), the finalize later
        // still (inside wrap_main).
        struct UnfDeferred {
            alpha: FieldVar<Fq>,
            beta: FieldVar<Fq>,
            gamma: FieldVar<Fq>,
            zeta: FieldVar<Fq>,
            xi: FieldVar<Fq>,
            cip_repr: FieldVar<Fq>,
            b_repr: FieldVar<Fq>,
            perm_repr: FieldVar<Fq>,
            bulletproof_challenges: Vec<FieldVar<Fq>>,
            sponge_digest_before_evaluations: FieldVar<Fq>,
            should_finalize: Boolean<Fq>,
        }
        let mut unf_deferred = Vec::with_capacity(w.unfinalized.len());
        for u in &w.unfinalized {
            let should_finalize: Boolean<Fq> = sys.compute(loc!(), |_| u.should_finalize)?;
            unf_deferred.push(UnfDeferred {
                alpha: w1(sys, u.alpha)?,
                beta: w1(sys, u.beta)?,
                gamma: w1(sys, u.gamma)?,
                zeta: w1(sys, u.zeta)?,
                xi: w1(sys, u.xi)?,
                cip_repr: w1(sys, u.cip_repr)?,
                b_repr: w1(sys, u.b_repr)?,
                perm_repr: w1(sys, u.perm_repr)?,
                bulletproof_challenges: wvec(sys, &u.bulletproof_challenges)?,
                sponge_digest_before_evaluations: w1(sys, u.sponge_digest_before_evaluations)?,
                should_finalize,
            });
        }
        // OCaml `exists prev_statement` (wrap_main.ml:191): the previous step
        // statement's public-input elements are witnessed here, before
        // `choose_key`.
        let expanded_step_statement_len: usize = w
            .step_statement
            .iter()
            .map(|slot| match slot {
                WrapStepStatementSlot::Field(_) => 2,
                WrapStepStatementSlot::Packed { .. } | WrapStepStatementSlot::Bool(_) => 1,
            })
            .sum();
        assert!(
            !w.step_statement_lagranges.is_empty(),
            "at least one branch Lagrange set"
        );
        for set in &w.step_statement_lagranges {
            assert_eq!(
                expanded_step_statement_len,
                set.len(),
                "one Lagrange slot per expanded step statement element"
            );
        }
        let mut elements = Vec::with_capacity(w.step_statement.len());
        // `prev_statement.proof_state` is not witnessed a second time before
        // `pack_statement`: thread every cvar already present in the
        // unfinalized proof state into its corresponding x_hat slot.
        let per_proof_slots = w
            .unfinalized
            .first()
            .map(|u| 12 + u.bulletproof_challenges.len())
            .unwrap_or(0);
        // The `messages_for_next_step` digest is BOTH a wrap public input
        // (slot 12) and a step-statement element fed to `x_hat`. OCaml threads
        // the same cvar into both instead of witnessing an equal private var,
        // so that use appears in PI 12's permutation cycle. Its FLATTENED
        // position is `step_statement_digest_slot` = `proofs * (17+TOCK_ROUNDS)`
        // — 0 only in the base case (the old `slot_index == 0` hack), non-zero
        // for update/merge (else PI 12 stays a singleton and the digest is
        // unconstrained: a soundness gap + the wrap PI-12 wiring divergence).
        let digest_flat_pos =
            crate::recursive_step::step_statement_digest_slot(expanded_step_statement_len);
        let mut flat_pos = 0usize;
        for (slot_index, slot) in w.step_statement.iter().enumerate() {
            let this_flat = flat_pos;
            flat_pos += match slot {
                WrapStepStatementSlot::Field(_) => 2,
                _ => 1,
            };
            match *slot {
                WrapStepStatementSlot::Field(value) => {
                    let prior = (per_proof_slots != 0
                        && slot_index < w.unfinalized.len() * per_proof_slots)
                        .then(|| {
                            let proof = slot_index / per_proof_slots;
                            let local = slot_index % per_proof_slots;
                            (&unf_deferred[proof], local)
                        });
                    let var = match prior {
                        Some((u, 0)) => u.cip_repr.clone(),
                        Some((u, 1)) => u.b_repr.clone(),
                        Some((u, 4)) => u.perm_repr.clone(),
                        _ => sys.compute(loc!(), move |_| value)?,
                    };
                    elements.push(StepStatementElement::Split(var));
                }
                WrapStepStatementSlot::Packed { value, num_bits } => {
                    let prior = (per_proof_slots != 0
                        && slot_index < w.unfinalized.len() * per_proof_slots)
                        .then(|| {
                            let proof = slot_index / per_proof_slots;
                            let local = slot_index % per_proof_slots;
                            (&unf_deferred[proof], local)
                        });
                    let var = match prior {
                        Some((u, 5)) => u.sponge_digest_before_evaluations.clone(),
                        Some((u, 6)) => u.beta.clone(),
                        Some((u, 7)) => u.gamma.clone(),
                        Some((u, 8)) => u.alpha.clone(),
                        Some((u, 9)) => u.zeta.clone(),
                        Some((u, 10)) => u.xi.clone(),
                        Some((u, local)) if local >= 11 && local < per_proof_slots - 1 => {
                            u.bulletproof_challenges[local - 11].clone()
                        }
                        _ if this_flat == digest_flat_pos => stmt[12].clone(),
                        _ => sys.compute(loc!(), move |_| value)?,
                    };
                    elements.push(StepStatementElement::Packed {
                        value: var,
                        num_bits,
                    });
                }
                WrapStepStatementSlot::Bool(_) => {
                    // OCaml threads prev_proof_state's own vars into
                    // pack_statement (wrap_main.ml:423-438): the statement's
                    // Bool slots ARE the should_finalize booleans witnessed
                    // above — re-witnessing one here would emit a second
                    // boolean check jsoo does not have.
                    let proof = slot_index / per_proof_slots;
                    debug_assert_eq!(slot_index % per_proof_slots, per_proof_slots - 1);
                    let bit = unf_deferred[proof].should_finalize.clone();
                    elements.push(StepStatementElement::Bool(bit));
                }
            }
        }
        // OCaml `wrap_main` selects the step VK with `choose_key which_branch`
        // over CONSTANT keys (`Inner_curve.constant`): each coordinate is
        // `sum_i which_branch_i · key_i` — for a single branch, `branch0 · c`,
        // sealed to a var (the 56 `Equal` at wrap_main.ml:204). No on-curve
        // check is emitted for the selected key: the jsoo dump has NO c=5
        // markers wired to the index-sponge absorbs (its pre-sponge markers
        // all belong to the openings/messages witnesses).
        let choose_pt =
            |sys: &mut RunState<Fq>, points: Vec<(Fq, Fq)>| -> SnarkyResult<Point<Fq>> {
                let choose_coordinate = |coordinate: usize| {
                    branches
                        .iter()
                        .zip(&points)
                        .fold(FieldVar::zero(), |sum, (branch, point)| {
                            let value = if coordinate == 0 { point.0 } else { point.1 };
                            sum + branch.to_field_var().scale(value)
                        })
                };
                let y = choose_coordinate(1).seal(sys, loc!())?;
                // `Double.map` constructs an OCaml pair.  Its tuple components
                // are evaluated right-to-left, so the y-coordinate seal is
                // emitted before the x-coordinate seal.
                let x = choose_coordinate(0).seal(sys, loc!())?;
                Ok(Point::new(x, y))
            };
        let choose_pts =
            |sys: &mut RunState<Fq>, points: Vec<Vec<(Fq, Fq)>>| -> SnarkyResult<Vec<Point<Fq>>> {
                let point_count = points[0].len();
                assert!(points.iter().all(|branch| branch.len() == point_count));
                let mut out = Vec::with_capacity(point_count);
                for index in (0..point_count).rev() {
                    out.push(choose_pt(
                        sys,
                        points.iter().map(|branch| branch[index]).collect(),
                    )?);
                }
                out.reverse();
                Ok(out)
            };
        // OCaml evaluates the fields of the `Step.map` result record from
        // right to left. Its vector map also invokes `f` from the last element
        // to the first. Allocate in that exact order, then assemble the Rust
        // record without adding constraints.
        //
        // The lookup / optional-gate commitments are the RIGHTMOST fields of the
        // `Plonk_verification_key_evals.Step.t` record, so OCaml allocates them
        // FIRST (before endomul_scalar), in reverse field order:
        // lookup_selector_ffmul, _range_check, _lookup, _xor, runtime_tables_selector,
        // lookup_table_ids, lookup_table_comm (reversed), then the gate selectors
        // rot, xor, ffadd, ffmul, range_check1, range_check0.
        // OCaml `assert_consistent` (wrap_main.ml:281-299) asserts each optional
        // commitment's `commitment_flag` equals its feature flag — on the SAME
        // sealed `is_yes` var that `choose_key` produced, not a freshly recomputed
        // sum. Capture those sealed flags here (constant `false` when the whole
        // lookup index is absent) so the consistency checks below reuse them.
        let mut cf_xor = Boolean::false_();
        let mut cf_rc0 = Boolean::false_();
        let mut cf_rc1 = Boolean::false_();
        let mut cf_ffadd = Boolean::false_();
        let mut cf_ffmul = Boolean::false_();
        let mut cf_rot = Boolean::false_();
        let mut cf_lut0 = Boolean::false_();
        let mut cf_lut1 = Boolean::false_();
        let mut cf_lut2 = Boolean::false_();
        let mut cf_lut3 = Boolean::false_();
        let mut cf_rt_sel = Boolean::false_();
        let mut cf_lookup_sel = Boolean::false_();
        let mut cf_xor_sel = Boolean::false_();
        let mut cf_rc_sel = Boolean::false_();
        let mut cf_ffmul_sel = Boolean::false_();
        let lookup: Option<crate::incrementally_verify::LookupVkComm<Fq>> = if let Some(shape) =
            w.lookup.clone()
        {
            // OCaml `choose_key` Maybe case (wrap_verifier.ml:269-320): the
            // coordinate sum is `just_sum + none_sum`, where `none_sum =
            // is_none · Inner_curve.one`. So a branch that does NOT carry this
            // optional commitment (Nothing) contributes the inner-curve
            // generator, NOT (0,0). The step VK commitments are Vesta points,
            // so `Inner_curve.one` is the Vesta generator. When every branch
            // carries the commitment (the `Just` special case, e.g. the
            // all-lookup wrap) this fallback never fires and the result is the
            // plain `Σ b·x`, matching OCaml's `justs,[],[]` path exactly.
            let gen_coords = {
                use ark_ec::{AffineRepr, CurveGroup};
                let g = Vesta::generator().into_group().into_affine();
                (g.x, g.y)
            };
            // Select one optional step-VK commitment across branches, matching
            // OCaml `choose_key`'s Maybe reduce (wrap_verifier.ml:269-319):
            //   sum = none_sum + just_sum
            // where `none_sum = is_none · generator` over the branches that do
            // NOT carry the commitment (`is_none = Σ absent bits`) and
            // `just_sum = Σ present bit · coord` over those that do. Crucially the
            // TERM ORDER of the sealed linear combination is: absent (generator)
            // terms FIRST, then present terms — this is the pairing jsoo emits,
            // and it differs from a naive branch-order `Σ bᵢ·coordᵢ` once two or
            // more branches carry the commitment (the double-generic seal pairs
            // terms differently). The all-present (`Just`) case has no absent
            // terms and reduces to the plain present sum, so it is unchanged.
            // Returns the selected commitment (None when no branch carries it) and
            // its OCaml `commitment_flag` (wrap_main.ml:273-279): `true_` for a
            // `Just` (every branch present), `false_` for `Nothing` (absent from
            // the shape), else the sealed `is_yes = Σ present bits` for a `Maybe`.
            // The SAME sealed flag var is reused by the digest-consistency checks
            // (jsoo asserts on this exact var, not a freshly recomputed sum).
            let select_opt = |sys: &mut RunState<Fq>,
                              get: &dyn Fn(&LookupBranchData) -> Option<(Fq, Fq)>,
                              present_in_shape: bool|
             -> SnarkyResult<(Option<Point<Fq>>, Boolean<Fq>)> {
                if !present_in_shape {
                    return Ok((None, Boolean::false_()));
                }
                let mut present: Vec<(&Boolean<Fq>, (Fq, Fq))> = Vec::new();
                let mut absent: Vec<&Boolean<Fq>> = Vec::new();
                for (b, bd) in branches.iter().zip(&branch_definitions) {
                    match bd.lookup.as_ref().and_then(|l| get(l)) {
                        Some(c) => present.push((b, c)),
                        None => absent.push(b),
                    }
                }
                let coord = |x_coord: bool| -> FieldVar<Fq> {
                    let gen = if x_coord { gen_coords.0 } else { gen_coords.1 };
                    let mut acc = FieldVar::zero();
                    for b in &absent {
                        acc = acc + b.to_field_var().scale(gen);
                    }
                    for (b, c) in &present {
                        let v = if x_coord { c.0 } else { c.1 };
                        acc = acc + b.to_field_var().scale(v);
                    }
                    acc
                };
                // OCaml seals the y-coordinate before the x-coordinate (Double.map
                // evaluates the pair right-to-left, matching `choose_pt`).
                let y = coord(false).seal(sys, loc!())?;
                let x = coord(true).seal(sys, loc!())?;
                // OCaml's final `Step.map` (wrap_verifier.ml:321-331) seals a Maybe
                // commitment as `Opt.Maybe (seal is_yes, seal coords)` — it seals
                // the presence flag `is_yes = Σ present bits` too, AFTER the coords
                // (constructor args evaluate right-to-left). A `Just` commitment
                // (no absent terms) seals only the coordinates and its flag is the
                // constant `true`. A single present branch needs no sum, so its
                // `is_yes` seal is a no-op (folds to the bare one-hot bit).
                let flag = if absent.is_empty() {
                    Boolean::true_()
                } else {
                    let is_yes = present
                        .iter()
                        .fold(FieldVar::zero(), |acc, (b, _)| acc + b.to_field_var());
                    Boolean::create_unsafe(is_yes.seal(sys, loc!())?)
                };
                Ok((Some(Point::new(x, y)), flag))
            };
            let (selector_ffmul, f_ffmul_sel) =
                select_opt(sys, &|l| l.selector_ffmul, shape.selector_ffmul.is_some())?;
            let (selector_range_check, f_rc_sel) = select_opt(
                sys,
                &|l| l.selector_range_check,
                shape.selector_range_check.is_some(),
            )?;
            let (selector_lookup, f_lookup_sel) =
                select_opt(sys, &|l| l.selector_lookup, shape.selector_lookup.is_some())?;
            let (selector_xor, f_xor_sel) =
                select_opt(sys, &|l| l.selector_xor, shape.selector_xor.is_some())?;
            let (runtime_tables_selector, f_rt_sel) = select_opt(
                sys,
                &|l| l.runtime_tables_selector,
                shape.runtime_tables_selector.is_some(),
            )?;
            let (table_ids, _f_table_ids) =
                select_opt(sys, &|l| l.table_ids, shape.table_ids.is_some())?;
            // lookup_table_comm: OCaml's `Vector.map` runs last-element-first, so
            // allocate the columns in reverse, then store forward for the digest.
            // Each column is a `Maybe` commitment (branches with a narrower table
            // do not carry it), so it goes through the same `just_sum + none_sum`
            // selection as the gate selectors. Column i's presence flag is
            // `table_width_at_least_(i+1)`, reused by the consistency checks.
            let mut lookup_table: Vec<Point<Fq>> = Vec::with_capacity(shape.lookup_table.len());
            let mut table_col_flags: Vec<Boolean<Fq>> =
                vec![Boolean::false_(); shape.lookup_table.len()];
            for i in (0..shape.lookup_table.len()).rev() {
                let (pt, flag) = select_opt(sys, &|l| l.lookup_table.get(i).copied(), true)?;
                lookup_table.push(pt.expect("lookup_table column present in shape"));
                table_col_flags[i] = flag;
            }
            lookup_table.reverse();
            let table_flag = |i: usize| -> Boolean<Fq> {
                table_col_flags.get(i).cloned().unwrap_or_else(Boolean::false_)
            };
            // The optional GATE selectors are sealed in REVERSE of the
            // `Plonk_verification_key_evals.Step.t` record field order
            // (plonk_verification_key_evals.ml:81-86 = xor, range_check0,
            // range_check1, foreign_field_add, foreign_field_mul, rot), because
            // OCaml's `choose_key`/`Step.map` evaluates the record right-to-left.
            // So the seal order is: rot, foreign_field_mul, foreign_field_add,
            // range_check1, range_check0, xor. In particular `xor_comm` is the
            // FIRST record field and thus sealed LAST (verified against jsoo's
            // xor+ffadd wrap: rust emitting xor first rotated the 4 gate-selector
            // commitments by one).
            let (gate_rot, f_rot_c) = select_opt(sys, &|l| l.gate_rot, shape.gate_rot.is_some())?;
            let (gate_foreign_field_mul, f_ffmul_c) = select_opt(
                sys,
                &|l| l.gate_foreign_field_mul,
                shape.gate_foreign_field_mul.is_some(),
            )?;
            let (gate_foreign_field_add, f_ffadd_c) = select_opt(
                sys,
                &|l| l.gate_foreign_field_add,
                shape.gate_foreign_field_add.is_some(),
            )?;
            let (gate_range_check1, f_rc1_c) =
                select_opt(sys, &|l| l.gate_range_check1, shape.gate_range_check1.is_some())?;
            let (gate_range_check0, f_rc0_c) =
                select_opt(sys, &|l| l.gate_range_check0, shape.gate_range_check0.is_some())?;
            let (gate_xor, f_xor_c) = select_opt(sys, &|l| l.gate_xor, shape.gate_xor.is_some())?;
            // The branch presence flag. Constant `true` when EVERY branch uses
            // lookup (Just, incl. single-branch base wraps). Otherwise it is
            // OCaml's `is_yes = Boolean.Unsafe.of_cvar (Σ present bits)`
            // (wrap_verifier.ml:290/307): a RAW sum of the present branches'
            // one-hot bits — NOT a Boolean OR. No gate is emitted here (the sum is
            // a linear combination, and `choose_key` already seals a per-commitment
            // copy of it in `select_opt`); a `Boolean::any` OR would be an extra
            // gate jsoo does not have. Gates the OptSponge lookup absorbs +
            // combine_table + digest alignment + joint_combiner (jsoo `Opt.Maybe`).
            let lookup_present: Vec<&Boolean<Fq>> = branches
                .iter()
                .zip(&branch_definitions)
                .filter(|(_, bd)| bd.lookup.is_some())
                .map(|(flag, _)| flag)
                .collect();
            let lookup_flag: Boolean<Fq> = if branch_definitions.is_empty()
                || lookup_present.len() == branch_definitions.len()
            {
                Boolean::true_()
            } else {
                let refs: Vec<FieldVar<Fq>> =
                    lookup_present.iter().map(|b| b.to_field_var()).collect();
                let sum = FieldVar::sum(&refs.iter().collect::<Vec<_>>());
                Boolean::create_unsafe(sum)
            };
            // OCaml `compute_joint_combiner` branches on the Opt state of the 2nd
            // lookup-table column (`table_width_at_least_2`) and the runtime-tables
            // selector (wrap_verifier.ml:1026-1072). When BOTH are definitely
            // absent (no branch has a width>=2 table and none uses runtime tables),
            // it takes the flat `(Nothing, Nothing)` path (1035): absorb sorted
            // columns with no inner fork. Otherwise (a width>=2 table appears in
            // some branch — e.g. xor's 3-column table) it forks (1057/1040).
            // range_check uses a single-column table, so ffadd-only programs are
            // `jc_table_absent = true`.
            let jc_table_absent = !branch_definitions.iter().any(|bd| {
                bd.lookup.as_ref().is_some_and(|l| {
                    l.lookup_table.len() >= 2 || l.runtime_tables_selector.is_some()
                })
            });
            // Hand the sealed commitment flags to the outer consistency checks.
            cf_xor = f_xor_c.clone();
            cf_rc0 = f_rc0_c.clone();
            cf_rc1 = f_rc1_c.clone();
            cf_ffadd = f_ffadd_c.clone();
            cf_ffmul = f_ffmul_c.clone();
            cf_rot = f_rot_c.clone();
            cf_lut0 = table_flag(0);
            cf_lut1 = table_flag(1);
            cf_lut2 = table_flag(2);
            cf_lut3 = table_flag(3);
            cf_rt_sel = f_rt_sel.clone();
            cf_lookup_sel = f_lookup_sel.clone();
            cf_xor_sel = f_xor_sel.clone();
            cf_rc_sel = f_rc_sel.clone();
            cf_ffmul_sel = f_ffmul_sel.clone();
            // Pair each optional commitment with its own sealed presence flag so
            // the vk-index absorb and `combine_commitments` gate it individually.
            Some(crate::incrementally_verify::LookupVkComm {
                flag: lookup_flag,
                joint_lookup_used: shape.joint_lookup_used,
                jc_table_absent,
                gate_range_check0: gate_range_check0.map(|p| (p, f_rc0_c.clone())),
                gate_range_check1: gate_range_check1.map(|p| (p, f_rc1_c.clone())),
                gate_foreign_field_mul: gate_foreign_field_mul.map(|p| (p, f_ffmul_c.clone())),
                gate_foreign_field_add: gate_foreign_field_add.map(|p| (p, f_ffadd_c.clone())),
                gate_xor: gate_xor.map(|p| (p, f_xor_c.clone())),
                gate_rot: gate_rot.map(|p| (p, f_rot_c.clone())),
                lookup_table: lookup_table
                    .into_iter()
                    .zip(table_col_flags.iter().cloned())
                    .collect(),
                table_ids: table_ids.map(|p| (p, _f_table_ids.clone())),
                runtime_tables_selector: runtime_tables_selector.map(|p| (p, f_rt_sel.clone())),
                selector_xor: selector_xor.map(|p| (p, f_xor_sel.clone())),
                selector_lookup: selector_lookup.map(|p| (p, f_lookup_sel.clone())),
                selector_range_check: selector_range_check.map(|p| (p, f_rc_sel.clone())),
                selector_ffmul: selector_ffmul.map(|p| (p, f_ffmul_sel.clone())),
            })
        } else {
            None
        };
        let endomul_scalar = choose_pt(
            sys,
            branch_definitions
                .iter()
                .map(|branch| branch.endomul_scalar)
                .collect(),
        )?;
        let emul = choose_pt(
            sys,
            branch_definitions
                .iter()
                .map(|branch| branch.emul)
                .collect(),
        )?;
        let mul = choose_pt(
            sys,
            branch_definitions.iter().map(|branch| branch.mul).collect(),
        )?;
        let complete_add = choose_pt(
            sys,
            branch_definitions
                .iter()
                .map(|branch| branch.complete_add)
                .collect(),
        )?;
        let psm = choose_pt(
            sys,
            branch_definitions.iter().map(|branch| branch.psm).collect(),
        )?;
        let generic = choose_pt(
            sys,
            branch_definitions
                .iter()
                .map(|branch| branch.generic)
                .collect(),
        )?;
        let coefficients = choose_pts(
            sys,
            branch_definitions
                .iter()
                .map(|branch| branch.coefficients.clone())
                .collect(),
        )?;
        let sigma_last = choose_pts(
            sys,
            branch_definitions
                .iter()
                .map(|branch| branch.sigma_last.clone())
                .collect(),
        )?;
        let sigma_init = choose_pts(
            sys,
            branch_definitions
                .iter()
                .map(|branch| branch.sigma_init.clone())
                .collect(),
        )?;
        let vk = VerificationKeyComm {
            generic,
            psm,
            complete_add,
            mul,
            emul,
            endomul_scalar,
            coefficients,
            sigma_init,
            sigma_last,
            lookup,
        };
        // OCaml `wrap_main.ml:216-300` consistency block: assert that each
        // optional commitment's presence flag equals the corresponding
        // (derived) feature flag from the statement's `plonk.feature_flags`.
        // `commitment_flag`: Just -> true_, Nothing -> false_, Maybe -> is_yes
        // (sum of the one-hot bits of the branches that carry it). The feature
        // flag: Yes (all branches) -> true_, No (none) -> false_, Maybe (some)
        // -> the witnessed statement slot. When a feature is Yes/No BOTH sides
        // fold to constants and `assert_equals` emits nothing (why nolookup /
        // alllookup / single-branch stay byte-identical); only Maybe (mixed)
        // branches emit real Generic gates, which shift `prev_step_accs` down
        // exactly as jsoo's mixed wrap does. Derived flags follow
        // `Plonk_types.Features.to_full` and are forced in OCaml's LAZY order
        // (driven by `table_width_at_least_1 = any[tw2; lprc; ffmul]`).
        {
            // Per-branch usage of each raw feature (false for no-lookup branches).
            let uses = |g: &dyn Fn(&LookupBranchData) -> bool| -> Vec<bool> {
                branch_definitions
                    .iter()
                    .map(|b| b.lookup.as_ref().map(|l| g(l)).unwrap_or(false))
                    .collect()
            };
            // One-hot bit sum over the branches where `present[k]` holds.
            let is_yes = |present: &[bool]| -> FieldVar<Fq> {
                let bits: Vec<FieldVar<Fq>> = branches
                    .iter()
                    .zip(present)
                    .filter(|(_, &p)| p)
                    .map(|(b, _)| b.to_field_var())
                    .collect();
                let refs: Vec<&FieldVar<Fq>> = bits.iter().collect();
                FieldVar::sum(&refs)
            };
            // `commitment_flag`: Just -> true_, Nothing -> false_, Maybe -> is_yes.
            let comm_flag = |present: &[bool]| -> Boolean<Fq> {
                if present.iter().all(|&p| p) {
                    Boolean::true_()
                } else if !present.iter().any(|&p| p) {
                    Boolean::false_()
                } else {
                    Boolean::create_unsafe(is_yes(present))
                }
            };
            // Raw feature flag: Yes -> true_, No -> false_, Maybe -> stmt slot.
            let feat_base = stmt.len() - 10;
            let raw_flag = |used: &[bool], slot_off: usize| -> Boolean<Fq> {
                if used.iter().all(|&u| u) {
                    Boolean::true_()
                } else if !used.iter().any(|&u| u) {
                    Boolean::false_()
                } else {
                    Boolean::create_unsafe(stmt[feat_base + slot_off].clone())
                }
            };

            // Raw feature statuses (Plonk_types.Features.to_data order).
            let f_rc0 = raw_flag(&uses(&|l| l.range_check0), 0);
            let f_rc1 = raw_flag(&uses(&|l| l.range_check1), 1);
            let f_ffadd = raw_flag(&uses(&|l| l.foreign_field_add), 2);
            let f_ffmul = raw_flag(&uses(&|l| l.foreign_field_mul), 3);
            let f_xor = raw_flag(&uses(&|l| l.xor), 4);
            let f_rot = raw_flag(&uses(&|l| l.rot), 5);
            let f_lookup = raw_flag(&uses(&|l| l.lookup), 6);
            let f_rt = raw_flag(&uses(&|l| l.uses_runtime_tables), 7);

            // Commitment presence flags: reuse the SAME sealed `is_yes` vars that
            // `select_opt`/`choose_key` produced (jsoo asserts on those exact vars).
            let _ = &comm_flag; // retained for documentation of the Maybe folding
            let c_xor = cf_xor;
            let c_rc0 = cf_rc0;
            let c_rc1 = cf_rc1;
            let c_ffadd = cf_ffadd;
            let c_ffmul = cf_ffmul;
            let c_rot = cf_rot;
            let c_lut0 = cf_lut0;
            let c_lut1 = cf_lut1;
            let c_lut2 = cf_lut2;
            let c_lut3 = cf_lut3;
            let c_rt_sel = cf_rt_sel;
            let c_lookup_sel = cf_lookup_sel;
            let c_xor_sel = cf_xor_sel;
            let c_rc_sel = cf_rc_sel;
            let c_ffmul_sel = cf_ffmul_sel;

            let ae = |sys: &mut RunState<Fq>, a: &Boolean<Fq>, b: &Boolean<Fq>| -> SnarkyResult<()> {
                a.to_field_var().assert_equals(sys, loc!(), &b.to_field_var())
            };

            // OCaml order (wrap_main.ml:284-299). Derived flags are computed in
            // LAZY force order, first forced by `table_width_at_least_1` at the
            // lookup_table_comm0 check.
            ae(sys, &c_xor, &f_xor)?; // xor
            ae(sys, &c_rc0, &f_rc0)?; // range_check0
            ae(sys, &c_rc1, &f_rc1)?; // range_check1
            ae(sys, &c_ffadd, &f_ffadd)?; // foreign_field_add
            ae(sys, &c_ffmul, &f_ffmul)?; // foreign_field_mul
            ae(sys, &c_rot, &f_rot)?; // rot
            // table_width_at_least_1 = any[table_width_at_least_2; lookup_pattern_range_check; ffmul]
            // Force order: tw2 (tw3=xor ||| lookup), then lprc (rc0|||rc1|||rot), then any.
            let tw3 = f_xor.clone(); // lookup_pattern_xor
            let tw2 = tw3.or(&f_lookup, loc!(), sys); // table_width_at_least_2
            let lprc = {
                let a = f_rc0.or(&f_rc1, loc!(), sys);
                a.or(&f_rot, loc!(), sys) // lookup_pattern_range_check
            };
            let tw1 = Boolean::any(&[&tw2, &lprc, &f_ffmul], sys, loc!())?;
            ae(sys, &c_lut0, &tw1)?; // table_width_at_least_1
            ae(sys, &c_lut1, &tw2)?; // table_width_at_least_2
            ae(sys, &c_lut2, &tw3)?; // table_width_3
            ae(sys, &c_lut3, &Boolean::false_())?; // lookup_table_comm3 <-> false
            ae(sys, &c_rt_sel, &f_rt)?; // runtime_tables
            ae(sys, &c_lookup_sel, &f_lookup)?; // lookup
            ae(sys, &c_xor_sel, &tw3)?; // lookup_pattern_xor
            ae(sys, &c_rc_sel, &lprc)?; // lookup_pattern_range_check
            ae(sys, &c_ffmul_sel, &f_ffmul)?; // foreign_field_mul
        }

        // OCaml witness order (wrap_main.ml): `prev_step_accs` (sg_olds), then
        // `openings_proof` (:440), then `messages` (:470).
        // `prev_step_accs` (wrap_main.ml:301-305) is witnessed ONCE and serves
        // both as `~sg_old` for the verifier and as the per-proof accumulator
        // in the previous-accumulator hashes (:425-431). The physical sg_olds
        // and the per-unfinalized prev_step_acc carry the same values in the
        // same logical values. The stored sg vector is in OCaml's physical
        // witness order, so the alias index is crossed below; a second witness
        // would add on-curve rows jsoo does not have.
        let sg_olds = mkpts(sys, &w.sg_olds)?;
        if !w.unfinalized.is_empty() {
            assert_eq!(
                sg_olds.len(),
                w.unfinalized.len(),
                "one physical sg_old per unfinalized proof"
            );
            for (k, u) in w.unfinalized.iter().enumerate() {
                let sg_index = w.sg_olds.len() - 1 - k;
                assert_eq!(
                    u.prev_step_acc, w.sg_olds[sg_index],
                    "prev_step_acc must alias sg_olds[{sg_index}]"
                );
            }
        }
        // `old_bp_chals` (wrap_main.ml:306): the old bulletproof challenge
        // vectors (both the finalize copy and the accumulator-hash copy).
        let mut finalize_old_bp_chals = Vec::with_capacity(w.unfinalized.len());
        for u in w.unfinalized.iter().rev() {
            let old_bulletproof_challenges = u
                .old_bulletproof_challenges
                .iter()
                .enumerate()
                .map(|(j, chals)| {
                    if j < u.constant_pad_challenges {
                        // Dummy pad below the program width: circuit
                        // constants (`Wrap_hack.Checked.pad_challenges`).
                        Ok(chals.iter().map(|&c| FieldVar::constant(c)).collect())
                    } else {
                        wvec(sys, chals)
                    }
                })
                .collect::<SnarkyResult<Vec<_>>>()?;
            finalize_old_bp_chals.push(old_bulletproof_challenges);
        }
        finalize_old_bp_chals.reverse();
        let cross_shared = w.unfinalized.len() == 2
            && w.unfinalized.iter().enumerate().all(|(i, u)| {
                u.hash_dummy_challenges.is_empty()
                    && u.hash_old_bulletproof_challenges
                        == w.unfinalized[1 - i].old_bulletproof_challenges
            });
        let mut unf_old_bp_chals = Vec::with_capacity(w.unfinalized.len());
        for (i, u) in w.unfinalized.iter().enumerate() {
            let hash_old_bulletproof_challenges = if u.hash_old_bulletproof_challenges
                == u.old_bulletproof_challenges
            {
                finalize_old_bp_chals[i].clone()
            } else if u
                .old_bulletproof_challenges
                .ends_with(&u.hash_old_bulletproof_challenges)
            {
                // Width-1 program: the accumulator hash absorbs the SAME
                // cvars as the finalize's real (trailing) vectors — the
                // constant dummy prefix was moved to `hash_dummy_challenges`
                // (`Wrap_hack.Checked`), so only the suffix is shared.
                finalize_old_bp_chals[i][u.old_bulletproof_challenges.len()
                    - u.hash_old_bulletproof_challenges.len()..]
                    .to_vec()
            } else if cross_shared {
                finalize_old_bp_chals[1 - i].clone()
            } else {
                u.hash_old_bulletproof_challenges
                    .iter()
                    .map(|chals| wvec(sys, chals))
                    .collect::<SnarkyResult<Vec<_>>>()?
            };
            unf_old_bp_chals.push((
                finalize_old_bp_chals[i].clone(),
                hash_old_bulletproof_challenges,
            ));
        }
        // `evals` (wrap_main.ml:341-349): the deferred evaluations of each
        // unfinalized proof, witnessed after the old challenges; the
        // finalize itself runs inside `wrap_main`, as in OCaml (:409-419).
        let mds: Vec<Vec<Fq>> = Pallas::sponge_params()
            .mds
            .iter()
            .map(|r| r.to_vec())
            .collect();
        let mut unfinalized = Vec::with_capacity(w.unfinalized.len());
        for (u, (deferred, (old_bp, hash_old_bp))) in w
            .unfinalized
            .iter()
            .zip(unf_deferred.into_iter().zip(unf_old_bp_chals.into_iter()))
        {
            let public_evals = [
                wvec(sys, &u.public_evals[0])?,
                wvec(sys, &u.public_evals[1])?,
            ];
            let mut fe = u.evals_flat.iter();
            let mut next_pe =
                |sys: &mut RunState<Fq>| -> SnarkyResult<crate::fr_sponge::PointEvalVar<Fq>> {
                    let &(a, b) = fe.next().unwrap();
                    Ok((vec![w1(sys, a)?], vec![w1(sys, b)?]))
                };
            let evals = crate::fr_sponge::AbsorbEvalsVar {
                w: (0..COLUMNS)
                    .map(|_| next_pe(sys))
                    .collect::<SnarkyResult<Vec<_>>>()?,
                coefficients: (0..COLUMNS)
                    .map(|_| next_pe(sys))
                    .collect::<SnarkyResult<Vec<_>>>()?,
                z: next_pe(sys)?,
                s: (0..PERMUTS - 1)
                    .map(|_| next_pe(sys))
                    .collect::<SnarkyResult<Vec<_>>>()?,
                generic_selector: next_pe(sys)?,
                poseidon_selector: next_pe(sys)?,
                complete_add_selector: next_pe(sys)?,
                mul_selector: next_pe(sys)?,
                emul_selector: next_pe(sys)?,
                endomul_scalar_selector: next_pe(sys)?,
            };
            let finalize_evals = FinalizeEvals {
                ft_eval1: w1(sys, u.ft_eval1)?,
                public_evals,
                evals,
            };
            let finalize_params = FinalizeParams {
                tokens: &u.finalize_tokens,
                domain: crate::ft_eval_circuit::FinalizeDomain::Fixed(u.finalize_domain),
                srs_log2: u.finalize_srs_log2,
                endo: u.finalize_endo,
                shifts: &u.finalize_shifts,
                endo_r: u.finalize_endo_r,
                mds: &mds,
                shift: ShiftKind::Type2,
            };
            // `Req.Wrap_domain_indices` (wrap_main.ml:356): the wrap-domain
            // index of the proof being finalized — `actual_wrap_domain_size`
            // maps log2 13/14/15 to 0/1/2 (common.ml:32-38).
            let wrap_log2 = u.finalize_domain.log_size_of_group;
            assert!(
                (13..=15).contains(&wrap_log2),
                "wrap domain log2 out of the possible range"
            );
            unfinalized.push(PerUnfinalized {
                finalize_params,
                finalize_evals,
                wrap_domain_index: Fq::from(wrap_log2 as u64 - 13),
                alpha: deferred.alpha,
                beta: deferred.beta,
                gamma: deferred.gamma,
                zeta: deferred.zeta,
                xi: deferred.xi,
                cip_repr: deferred.cip_repr,
                b_repr: deferred.b_repr,
                perm_repr: deferred.perm_repr,
                bulletproof_challenges: deferred.bulletproof_challenges,
                sponge_digest_before_evaluations: deferred.sponge_digest_before_evaluations,
                should_finalize: deferred.should_finalize,
                old_bulletproof_challenges: old_bp,
                prev_step_acc: sg_olds[sg_olds.len() - 1 - unfinalized.len()].clone(),
                hash_dummy_challenges: u.hash_dummy_challenges.clone(),
                hash_old_bulletproof_challenges: hash_old_bp,
            });
        }
        // `Generators.h` is `Inner_curve.constant (Lazy.force Generators.h)`
        // in OCaml — a fixed SRS point embedded as a circuit constant, never
        // witnessed or checked on-curve (wrap_verifier.ml:618, :965).
        let h = cpt(w.h);
        let t1 = ShiftedScalar::Type1;
        // `openings_proof` and `messages` are witnessed inside `wrap_main`
        // (via this closure) so their `exists` constraints land after the
        // finalize/hash-prev block, exactly as wrap_main.ml:440-477.
        let h_for_openings = h.clone();
        let witness_proof =
            |sys: &mut RunState<Fq>| -> SnarkyResult<(OpeningProof<Fq>, Messages<Fq>)> {
                let mut lr = vec![];
                for &(l, r) in &w.lr {
                    lr.push((mkpt(sys, l)?, mkpt(sys, r)?));
                }
                let z1_repr = w1(sys, w.z1_repr)?;
                let z2_repr = w1(sys, w.z2_repr)?;
                // `Bulletproof.wrap_typ` checks the two Other_field.Packed
                // representatives after witnessing `lr` and before witnessing
                // delta / sg. This is the 14-row gap between the two pre-sponge
                // on-curve marker groups in the jsoo circuit.
                let forbidden = crate::shifted_value::forbidden_shifted_values_fq();
                for slot in [&z1_repr, &z2_repr] {
                    let mut eqs = Vec::with_capacity(forbidden.len());
                    for &value in &forbidden {
                        eqs.push(other_field_equal(sys, slot, value, false)?);
                    }
                    let eq_refs: Vec<&Boolean<Fq>> = eqs.iter().collect();
                    let any = Boolean::any(&eq_refs, sys, loc!())?;
                    any.not().to_field_var().assert_equals(
                        sys,
                        loc!(),
                        &FieldVar::constant(Fq::from(1u64)),
                    )?;
                }
                let openings = OpeningProof {
                    lr,
                    delta: mkpt(sys, w.delta)?,
                    z1: t1(z1_repr),
                    z2: t1(z2_repr),
                    challenge_polynomial_commitment: mkpt(sys, w.sg)?,
                    h_generator: h_for_openings.clone(),
                };
                let messages = Messages {
                    w_comm: w
                        .w_comm
                        .iter()
                        .map(|&p| Ok(vec![mkpt(sys, p)?]))
                        .collect::<SnarkyResult<Vec<_>>>()?,
                    z_comm: vec![mkpt(sys, w.z_comm)?],
                    t_comm: w
                        .t_comm
                        .iter()
                        .map(|&p| mkpt(sys, p))
                        .collect::<SnarkyResult<Vec<_>>>()?,
                    lookup: if w.lookup.is_some() {
                        // OCaml `Messages.Lookup.wrap_opt_typ` (plonk_types.ml:1627)
                        // wraps the lookup section in `Opt uses_lookup` and splits
                        // sorted into a fixed vector of `Lookup_sorted_minus_1.n`=4
                        // plus a `sorted_5th_column: Opt lookups_per_row_4`. For a
                        // mixed feature set both Opts are `Maybe` → each `maybe_typ`
                        // witnesses+boolean-checks a flag var. jsoo emits these two
                        // booleans interspersed as `bool, 4 sorted pts, bool, 5th pt`
                        // (constraint dump: Boolean(Var 334) then Boolean(Var 343)).
                        // Emit them only when Maybe (Yes/No fold → keeps alllookup /
                        // single-branch byte-identical).
                        let present: Vec<bool> = if w.branches.is_empty() {
                            vec![w.lookup.is_some()]
                        } else {
                            w.branches.iter().map(|b| b.lookup.is_some()).collect()
                        };
                        let has_5th: Vec<bool> = if w.branches.is_empty() {
                            vec![w
                                .lookup
                                .as_ref()
                                .map(|l| l.sorted_count() >= 5)
                                .unwrap_or(false)]
                        } else {
                            w.branches
                                .iter()
                                .map(|b| {
                                    b.lookup.as_ref().map(|l| l.sorted_count() >= 5).unwrap_or(false)
                                })
                                .collect()
                        };
                        let is_maybe = |v: &[bool]| v.iter().any(|&p| p) && !v.iter().all(|&p| p);
                        let uses_lookups_maybe = is_maybe(&present);
                        let lppr4_maybe = is_maybe(&has_5th);
                        // outer `Opt uses_lookup` Maybe flag: witness + boolean-check
                        // when Maybe, else constant true (Yes). Captured as the
                        // `Opt.Maybe` flag threaded through the lookup verification.
                        let flag = if uses_lookups_maybe {
                            // jsoo threads the STATEMENT's uses_lookups slot
                            // (stmt[38]) as this flag — its copy cycle spans the
                            // joint_combiner / combined_table / combine uses. A
                            // freshly-witnessed var would form an isolated cycle
                            // (sigma mismatch). Keep the messages Opt boolean
                            // check (part A gate structure).
                            let b = Boolean::create_unsafe(stmt[stmt.len() - 2].clone());
                            b.check(sys, loc!())?;
                            b
                        } else {
                            Boolean::true_()
                        };
                        let n_fixed = w.lookup_sorted.len().min(4);
                        let mut sorted = Vec::with_capacity(w.lookup_sorted.len());
                        for &p in &w.lookup_sorted[..n_fixed] {
                            sorted.push(vec![mkpt(sys, p)?]);
                        }
                        // `sorted_5th_column: Opt lookups_per_row_4` Maybe flag.
                        let lppr4_flag = if lppr4_maybe {
                            let selected_has_5th = if w.branches.is_empty() {
                                w.lookup
                                    .as_ref()
                                    .map(|l| l.sorted_count() >= 5)
                                    .unwrap_or(false)
                            } else {
                                w.branches
                                    .get(w.which_branch)
                                    .and_then(|branch| branch.lookup.as_ref())
                                    .map(|l| l.sorted_count() >= 5)
                                    .unwrap_or(false)
                            };
                            let f = sys.compute(loc!(), move |_| {
                                if selected_has_5th {
                                    Fq::one()
                                } else {
                                    Fq::from(0u64)
                                }
                            })?;
                            let b = Boolean::create_unsafe(f);
                            b.check(sys, loc!())?;
                            b
                        } else {
                            Boolean::true_()
                        };
                        for &p in &w.lookup_sorted[n_fixed..] {
                            sorted.push(vec![mkpt(sys, p)?]);
                        }
                        let aggreg = vec![mkpt(sys, w.lookup_aggreg)?];
                        let runtime = match w.lookup_runtime {
                            Some(p) => Some(vec![mkpt(sys, p)?]),
                            None => None,
                        };
                        Some(crate::incrementally_verify::LookupMsgComm {
                            sorted,
                            aggreg,
                            runtime,
                            flag,
                            lppr4_flag,
                        })
                    } else {
                        None
                    },
                };
                Ok((openings, messages))
            };
        // The verifier-index digest is now computed inside
        // `incrementally_verify_proof` (`IndexDigest::ComputeFromVk`), exactly
        // as OCaml's "absorb verifier index" — no caller-side digest here.
        let advice = Advice {
            combined_inner_product: t1(cip),
            b: t1(b),
            perm: t1(perm),
            zeta_to_srs_length: t1(zsl),
            zeta_to_domain_size: t1(zds),
        };
        let claimed = Claimed {
            beta,
            gamma,
            alpha,
            zeta,
            sponge_digest_before_evaluations: sponge_digest,
            bulletproof_challenges: bp,
            // The statement's joint_combiner scalar is the LAST slot (slot 39 of
            // the 40-slot layout: feature_flags[8] then joint_combiner opt = flag
            // + scalar). Only asserted for lookup branches (OCaml
            // `assert_eq_plonk` includes it only when the circuit uses lookups).
            joint_combiner: if w.lookup.is_some() {
                Some(stmt[STMT_LEN - 1].clone())
            } else {
                None
            },
        };

        // OCaml `lagrange_with_correction` (wrap_verifier.ml:382): if every
        // branch shares one step domain the constants are used directly;
        // otherwise the per-branch constants combine through the which_branch
        // one-hot INSIDE the x_hat term loop (StatementLagranges::OneHot), so
        // the materialization rows land in the verify region as in jsoo.
        let lagrange_sets = &w.step_statement_lagranges;
        let hetero =
            lagrange_sets.len() > 1 && lagrange_sets.iter().any(|set| set != &lagrange_sets[0]);
        let prepared: Vec<(Point<Fq>, Point<Fq>)>;
        let lagranges: crate::public_input::StatementLagranges<'_, Fq> = if branches.is_empty()
            || lagrange_sets.len() != branch_count
        {
            // Branchless legacy wraps and structural donor passes (a single
            // placeholder set for many branches): plain constants.
            prepared = lagrange_sets[0]
                .iter()
                .map(|&(l, c)| (cpt(l), cpt(c)))
                .collect();
            crate::public_input::StatementLagranges::Prepared(&prepared)
        } else {
            assert_eq!(
                lagrange_sets.len(),
                branch_count,
                "one Lagrange set per branch"
            );
            // jsoo's all-equal shortcut only folds the CORRECTED pairs; the
            // plain `lagrange` terms always mask through which_branch.
            crate::public_input::StatementLagranges::OneHot {
                sets: lagrange_sets,
                branches: &branches,
                corrected_constant: !hetero,
            }
        };

        let params = groupmap::BWParameters::<VestaParameters>::setup();
        let _out = wrap_main::<Fq, VestaParameters, _>(
            sys,
            loc!(),
            &unfinalized,
            &actual_proofs_verified_mask,
            &sg_olds,
            &vk,
            &elements,
            &lagranges,
            &h,
            witness_proof,
            &advice,
            &xi,
            &claimed,
            &msgs_wrap_digest,
            &w.new_acc_dummies,
            &params,
            crate::endo::tock::base(),
            <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1,
            255,
        )?;
        Ok(())
    }
}

fn fp_to_fq(x: Fp) -> Fq {
    Fq::from_le_bytes_mod_order(&x.into_bigint().to_bytes_le())
}

/// The base-case pickles proof plus everything the *next* (recursive) step
/// proof consumes: the wrap proof and its statement, both verifier wrappers,
/// and the underlying step proof (whose evaluations the recursive finalize
/// re-checks).
pub struct BaseCaseProof<A: StepApp, const ROUNDS: usize, const STMT_LEN: usize> {
    pub statement: Vec<Fq>,
    pub stable_statement: crate::mina_bin_prot::WrapStatementMinimalV1,
    pub proof: kimchi::proof::ProverProof<Pallas, IpaProof<Pallas, FULL_ROUNDS>, FULL_ROUNDS>,
    pub step_proof: kimchi::proof::ProverProof<Vesta, IpaProof<Vesta, FULL_ROUNDS>, FULL_ROUNDS>,
    pub step_verifier: snarky::api::VerifierIndexWrapper<StepCircuit<A>>,
    pub wrap_verifier: snarky::api::VerifierIndexWrapper<WrapCircuit<ROUNDS, STMT_LEN>>,
    /// The actual wrap verification-key commitments hashed by the step proof.
    pub wrap_vk_pts: Vec<(Fp, Fp)>,
}

/// Network-facing Mina encoding for a base-case Pickles proof.
///
/// The native proof remains available for local verification; this artifact
/// carries the stable Mina bytes needed at API boundaries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinaWrapProof {
    pub statement: Vec<Fq>,
    pub wrap_wire_proof: Vec<u8>,
    pub side_loaded_verification_key: String,
    pub wrap_recursion_commitments: Vec<(Fp, Fp)>,
    pub wrap_recursion_challenges: Vec<Vec<Fq>>,
}

/// JSON-safe envelope intended for JS/o1js consumers.
///
/// Field elements are decimal strings to preserve full Pasta precision in
/// JavaScript. The wrapped Mina bin_prot proof bytes are base64 encoded, and
/// the side-loaded verification key remains Mina Base58Check.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct O1jsWrapProofJson {
    pub version: u8,
    pub statement: Vec<String>,
    pub wrap_wire_proof_base64: String,
    pub side_loaded_verification_key_base58: String,
    pub wrap_recursion_commitments: Vec<(String, String)>,
    pub wrap_recursion_challenges: Vec<Vec<String>>,
}

#[deprecated(note = "use MinaWrapProof; this wrap proof envelope is no longer base-case specific")]
pub type MinaBaseCaseProof = MinaWrapProof;

#[deprecated(note = "use O1jsWrapProofJson; this JSON envelope is no longer base-case specific")]
pub type O1jsBaseCaseProofJson = O1jsWrapProofJson;

impl MinaWrapProof {
    pub const O1JS_JSON_VERSION: u8 = 1;

    pub fn to_o1js_json_value(&self) -> O1jsWrapProofJson {
        O1jsWrapProofJson {
            version: Self::O1JS_JSON_VERSION,
            statement: self
                .statement
                .iter()
                .map(|field| field.to_string())
                .collect(),
            wrap_wire_proof_base64: BASE64_STANDARD.encode(&self.wrap_wire_proof),
            side_loaded_verification_key_base58: self.side_loaded_verification_key.clone(),
            wrap_recursion_commitments: self
                .wrap_recursion_commitments
                .iter()
                .map(|(x, y)| (x.to_string(), y.to_string()))
                .collect(),
            wrap_recursion_challenges: self
                .wrap_recursion_challenges
                .iter()
                .map(|challenges| challenges.iter().map(ToString::to_string).collect())
                .collect(),
        }
    }

    pub fn from_o1js_json_value(value: O1jsWrapProofJson) -> Result<Self, BaseCaseBackendError> {
        if value.version != Self::O1JS_JSON_VERSION {
            return Err(BaseCaseBackendError::O1jsJsonVersion(value.version));
        }
        let statement = value
            .statement
            .iter()
            .map(|field| {
                field
                    .parse::<Fq>()
                    .map_err(|_| BaseCaseBackendError::O1jsJsonField)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let wrap_wire_proof = BASE64_STANDARD
            .decode(value.wrap_wire_proof_base64)
            .map_err(|_| BaseCaseBackendError::O1jsJsonProofBytes)?;
        let wrap_recursion_commitments = value
            .wrap_recursion_commitments
            .iter()
            .map(|(x, y)| {
                Ok((
                    x.parse::<Fp>()
                        .map_err(|_| BaseCaseBackendError::O1jsJsonField)?,
                    y.parse::<Fp>()
                        .map_err(|_| BaseCaseBackendError::O1jsJsonField)?,
                ))
            })
            .collect::<Result<Vec<_>, BaseCaseBackendError>>()?;
        let wrap_recursion_challenges = value
            .wrap_recursion_challenges
            .iter()
            .map(|challenges| {
                challenges
                    .iter()
                    .map(|challenge| {
                        challenge
                            .parse::<Fq>()
                            .map_err(|_| BaseCaseBackendError::O1jsJsonField)
                    })
                    .collect()
            })
            .collect::<Result<Vec<_>, BaseCaseBackendError>>()?;
        Ok(Self {
            statement,
            wrap_wire_proof,
            side_loaded_verification_key: value.side_loaded_verification_key_base58,
            wrap_recursion_commitments,
            wrap_recursion_challenges,
        })
    }

    pub fn to_o1js_json_string(&self) -> Result<String, BaseCaseBackendError> {
        serde_json::to_string(&self.to_o1js_json_value())
            .map_err(|_| BaseCaseBackendError::O1jsJsonSerialization)
    }

    pub fn from_o1js_json_string(value: &str) -> Result<Self, BaseCaseBackendError> {
        let value =
            serde_json::from_str(value).map_err(|_| BaseCaseBackendError::O1jsJsonSerialization)?;
        Self::from_o1js_json_value(value)
    }
}

impl<A: StepApp, const ROUNDS: usize, const STMT_LEN: usize> BaseCaseProof<A, ROUNDS, STMT_LEN> {
    pub fn to_mina_network_proof(&self) -> Result<MinaWrapProof, BaseCaseBackendError> {
        let wrap_wire_proof = crate::mina_bin_prot::WrapWireProofV1::from_prover_proof(&self.proof)
            .and_then(|proof| proof.to_bin_prot())
            .map_err(|_| BaseCaseBackendError::MinaProofEncoding)?;
        let step_domain_log2 = self.step_verifier.index.domain.log_size_of_group as u8;
        let side_loaded_verification_key =
            SideLoadedVerificationKey::from_wrap_verifier(step_domain_log2, &self.wrap_verifier)
                .map_err(|_| BaseCaseBackendError::MinaVerificationKeyEncoding)?
                .to_stable_v2_base58()
                .map_err(|_| BaseCaseBackendError::MinaVerificationKeyEncoding)?;
        Ok(MinaWrapProof {
            statement: self.statement.clone(),
            wrap_wire_proof,
            side_loaded_verification_key,
            wrap_recursion_commitments: self
                .proof
                .prev_challenges
                .iter()
                .map(|challenge| {
                    let point = challenge.comm.chunks[0];
                    (point.x, point.y)
                })
                .collect(),
            wrap_recursion_challenges: self
                .proof
                .prev_challenges
                .iter()
                .map(|challenge| challenge.chals.clone())
                .collect(),
        })
    }

    pub fn ensure_mina_network_proof_matches(
        &self,
        encoded: &MinaWrapProof,
    ) -> Result<(), BaseCaseBackendError> {
        if encoded != &self.to_mina_network_proof()? {
            return Err(BaseCaseBackendError::MinaEncodingMismatch);
        }
        crate::mina_bin_prot::WrapWireProofV1::from_bin_prot(&encoded.wrap_wire_proof)
            .map_err(|_| BaseCaseBackendError::MinaProofEncoding)?;
        SideLoadedVerificationKey::from_stable_v2_base58(
            self.step_verifier.index.domain.log_size_of_group as u8,
            &encoded.side_loaded_verification_key,
        )
        .map_err(|_| BaseCaseBackendError::MinaVerificationKeyEncoding)?;
        Ok(())
    }

    pub fn to_mina_stable_v3(
        &self,
    ) -> Result<crate::mina_bin_prot::WrapProofBaseV3, BaseCaseBackendError> {
        crate::mina_bin_prot::WrapProofBaseV3::from_proofs_with_statement(
            self.stable_statement.clone(),
            &self.step_proof,
            &self.proof,
        )
        .map_err(|_| BaseCaseBackendError::MinaProofEncoding)
    }
}

/// Returns a wrap verifier index's 28 commitments in Pickles' canonical
/// sigma, coefficients, selector order.
pub fn wrap_verification_key_points<const ROUNDS: usize, const STMT_LEN: usize>(
    verifier: &snarky::api::VerifierIndexWrapper<WrapCircuit<ROUNDS, STMT_LEN>>,
) -> Vec<(Fp, Fp)> {
    let index = &verifier.index;
    let point = |p: &Pallas| (p.x, p.y);
    let mut points = Vec::with_capacity(28);
    points.extend(
        index
            .sigma_comm
            .iter()
            .map(|commitment| point(&commitment.chunks[0])),
    );
    points.extend(
        index
            .coefficients_comm
            .iter()
            .map(|commitment| point(&commitment.chunks[0])),
    );
    points.push(point(&index.generic_comm.chunks[0]));
    points.push(point(&index.psm_comm.chunks[0]));
    points.push(point(&index.complete_add_comm.chunks[0]));
    points.push(point(&index.mul_comm.chunks[0]));
    points.push(point(&index.emul_comm.chunks[0]));
    points.push(point(&index.endomul_scalar_comm.chunks[0]));
    assert_eq!(points.len(), 28);
    points
}

/// Compiles the wrap circuit in two passes to break the Pickles VK cycle.
///
/// The bootstrap pass determines the wrap index from the circuit shape. The
/// final pass rebuilds the step proof with those real 28 commitments in its
/// accumulator digest, recompiles the wrap, asserts index stability, and
/// returns only the final proof.
pub fn prove_base_case_two_pass<A: StepApp + Clone, const ROUNDS: usize, const STMT_LEN: usize>(
    app: A,
    witness: A::Witness,
) -> BaseCaseProof<A, ROUNDS, STMT_LEN>
where
    A::Witness: Clone,
{
    // The bootstrap key must satisfy the step circuit's on-curve checks, so
    // use distinct multiples of the Pallas generator as placeholder points.
    let bootstrap_points = {
        use ark_ec::{AffineRepr, CurveGroup};
        let g = Pallas::generator().into_group();
        (1..=28u64)
            .map(|i| {
                let p = (g * mina_curves::pasta::Fq::from(i)).into_affine();
                (p.x, p.y)
            })
            .collect()
    };
    let (step_prover, step_verifier, bootstrap_verifier) =
        match build_base_case::<A, ROUNDS, STMT_LEN>(
            app.clone(),
            witness.clone(),
            bootstrap_points,
            false,
            None,
            None,
            None,
            None,
        ) {
            BaseCaseBuild::Compiled {
                step_prover,
                step_verifier,
                wrap_prover: _,
                wrap_verifier,
            } => (step_prover, step_verifier, wrap_verifier),
            BaseCaseBuild::Proof { .. } => unreachable!("bootstrap mode only compiles the wrap VK"),
        };
    let actual_points = wrap_verification_key_points(&bootstrap_verifier);
    let final_proof = match build_base_case::<A, ROUNDS, STMT_LEN>(
        app,
        witness,
        actual_points.clone(),
        true,
        Some((step_prover, step_verifier)),
        None,
        None,
        None,
    ) {
        BaseCaseBuild::Proof { proof, .. } => proof,
        BaseCaseBuild::Compiled { .. } => unreachable!("final mode returns a complete proof"),
    };
    assert_eq!(
        wrap_verification_key_points(&final_proof.wrap_verifier),
        actual_points,
        "wrap verification key changed between compilation passes"
    );
    final_proof
}

/// Concrete [`CompiledRuleBackend`] for a Pickles base (`N0`) rule.
///
/// Proof creation uses the two-pass real-wrap-VK pipeline. Verification checks
/// both the Kimchi wrap proof and the binding between the caller's public
/// application state and the accumulator digest in the wrap statement.
pub struct BaseCaseRuleBackend<A: StepApp, const ROUNDS: usize, const STMT_LEN: usize> {
    rule_id: RuleId,
    app: A,
}

impl<A: StepApp, const ROUNDS: usize, const STMT_LEN: usize>
    BaseCaseRuleBackend<A, ROUNDS, STMT_LEN>
{
    pub fn compile(rule: &InductiveRule, app: A) -> Result<Self, BaseCaseBackendError> {
        if rule.proofs_verified != ProofsVerified::N0 {
            return Err(BaseCaseBackendError::ExpectedBaseRule(rule.id));
        }
        Ok(Self {
            rule_id: rule.id,
            app,
        })
    }

    pub fn rule_id(&self) -> RuleId {
        self.rule_id
    }

    pub fn prove_with_mina_encoding(
        &mut self,
        public_input: &Vec<Fp>,
        witness: A::Witness,
    ) -> Result<(BaseCaseProof<A, ROUNDS, STMT_LEN>, MinaWrapProof), BaseCaseBackendError>
    where
        A: Clone,
        A::Witness: Clone,
    {
        let proof = <Self as CompiledRuleBackend>::prove(self, public_input, witness)?;
        let encoded = proof.to_mina_network_proof()?;
        Ok((proof, encoded))
    }

    pub fn verify_with_mina_encoding(
        &self,
        public_input: &Vec<Fp>,
        proof: &BaseCaseProof<A, ROUNDS, STMT_LEN>,
        encoded: &MinaWrapProof,
    ) -> Result<(), BaseCaseBackendError>
    where
        A: Clone,
        A::Witness: Clone,
    {
        <Self as CompiledRuleBackend>::verify(self, public_input, proof)?;
        proof.ensure_mina_network_proof_matches(encoded)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BaseCaseBackendError {
    ExpectedBaseRule(RuleId),
    PublicStateMismatch,
    WrapKeyMismatch,
    InvalidStatementLength(usize),
    InvalidWrapProof,
    MinaProofEncoding,
    MinaVerificationKeyEncoding,
    MinaEncodingMismatch,
    O1jsJsonSerialization,
    O1jsJsonVersion(u8),
    O1jsJsonField,
    O1jsJsonProofBytes,
}

impl<A: StepApp + Clone, const ROUNDS: usize, const STMT_LEN: usize> CompiledRuleBackend
    for BaseCaseRuleBackend<A, ROUNDS, STMT_LEN>
where
    A::Witness: Clone,
{
    type PublicInput = Vec<Fp>;
    type Witness = A::Witness;
    type Proof = BaseCaseProof<A, ROUNDS, STMT_LEN>;
    type Error = BaseCaseBackendError;

    fn prove(
        &mut self,
        public_input: &Self::PublicInput,
        witness: Self::Witness,
    ) -> Result<Self::Proof, Self::Error> {
        if self.app.state(&witness) != *public_input {
            return Err(BaseCaseBackendError::PublicStateMismatch);
        }
        Ok(prove_base_case_two_pass::<A, ROUNDS, STMT_LEN>(
            self.app.clone(),
            witness,
        ))
    }

    fn verify(
        &self,
        public_input: &Self::PublicInput,
        proof: &Self::Proof,
    ) -> Result<(), Self::Error> {
        let actual_vk = wrap_verification_key_points(&proof.wrap_verifier);
        if actual_vk != proof.wrap_vk_pts {
            return Err(BaseCaseBackendError::WrapKeyMismatch);
        }
        let digest = crate::hash_messages::hash_messages_for_next_step_proof_ref(
            Vesta::sponge_params(),
            &actual_vk,
            public_input,
            &[],
            &[],
        );
        if proof.statement.len() != STMT_LEN {
            return Err(BaseCaseBackendError::InvalidStatementLength(
                proof.statement.len(),
            ));
        }
        // Wrap.Statement.to_data stores the next-step message digest at slot
        // 12, before bulletproof challenges, branch data and feature flags.
        if proof.statement[12] != fp_to_fq(digest) {
            return Err(BaseCaseBackendError::PublicStateMismatch);
        }
        let statement: [Fq; STMT_LEN] =
            proof
                .statement
                .clone()
                .try_into()
                .map_err(|statement: Vec<Fq>| {
                    BaseCaseBackendError::InvalidStatementLength(statement.len())
                })?;
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            proof.wrap_verifier.verify::<PallasBase, PallasScalar>(
                proof.proof.clone(),
                statement,
                (),
            );
        }))
        .map_err(|_| BaseCaseBackendError::InvalidWrapProof)
    }
}

/// Proves one application execution through the full base-case pipeline and
/// verifies the resulting wrap proof. `ROUNDS` must match the step circuit's
/// IPA round count (log2 of its compiled domain).
pub fn prove_base_case<A: StepApp, const ROUNDS: usize, const STMT_LEN: usize>(
    app: A,
    witness: A::Witness,
    wrap_vk_pts: Vec<(Fp, Fp)>,
) -> BaseCaseProof<A, ROUNDS, STMT_LEN> {
    prove_base_case_with_wrap_dump(app, witness, wrap_vk_pts).0
}

/// The wrap circuit of a base-case proof, in the `{ public_input_size,
/// gates }` shape shared with the jsoo `prover_to_json` dumps — the Fq half
/// of the gate-level parity diff against OCaml Pickles.
#[derive(serde::Serialize)]
pub struct WrapCircuitDump {
    pub public_input_size: usize,
    pub gates: Vec<kimchi::circuits::gate::CircuitGate<Fq>>,
    /// Debug-only: per-gate emission labels aligned 1:1 with `gates`.
    #[serde(default)]
    pub labels: Vec<String>,
}

type StepIndexes<A> = (
    snarky::api::ProverIndexWrapper<StepCircuit<A>>,
    snarky::api::VerifierIndexWrapper<StepCircuit<A>>,
);
pub(crate) type WrapIndexes<const ROUNDS: usize, const STMT_LEN: usize> = (
    snarky::api::ProverIndexWrapper<WrapCircuit<ROUNDS, STMT_LEN>>,
    snarky::api::VerifierIndexWrapper<WrapCircuit<ROUNDS, STMT_LEN>>,
);
pub(crate) type RawWrapIndex =
    kimchi::prover_index::ProverIndex<FULL_ROUNDS, Pallas, poly_commitment::ipa::SRS<Pallas>>;

/// Program-level data baked into a shared width-0 Wrap. A base proof still
/// carries the commitments of its selected Step branch at the top level, but
/// the circuit selects the matching constants from these complete branch and
/// Lagrange tables via `which_branch`.
#[derive(Clone)]
pub(crate) struct SharedBaseWrapData {
    pub which_branch: usize,
    pub branches: Vec<WrapBranchData>,
    pub step_statement_lagranges: Vec<Vec<((Fq, Fq), (Fq, Fq))>>,
}

pub(crate) enum BaseCaseBuild<A: StepApp, const ROUNDS: usize, const STMT_LEN: usize> {
    Compiled {
        step_prover: snarky::api::ProverIndexWrapper<StepCircuit<A>>,
        step_verifier: snarky::api::VerifierIndexWrapper<StepCircuit<A>>,
        wrap_prover: snarky::api::ProverIndexWrapper<WrapCircuit<ROUNDS, STMT_LEN>>,
        wrap_verifier: snarky::api::VerifierIndexWrapper<WrapCircuit<ROUNDS, STMT_LEN>>,
    },
    Proof {
        proof: BaseCaseProof<A, ROUNDS, STMT_LEN>,
        dump: WrapCircuitDump,
        step_indexes: StepIndexes<A>,
        wrap_indexes: WrapIndexes<ROUNDS, STMT_LEN>,
    },
}

/// Reusable base-case prover indexes. Compilation performs the two Pickles
/// key-discovery passes once; subsequent proofs regenerate witnesses while
/// reusing both the Step and final Wrap indexes.
pub struct CompiledBaseCase<A: StepApp, const ROUNDS: usize, const STMT_LEN: usize> {
    pub(crate) app: A,
    pub(crate) wrap_vk_pts: Vec<(Fp, Fp)>,
    pub(crate) step_indexes: Option<StepIndexes<A>>,
    pub(crate) wrap_indexes: Option<WrapIndexes<ROUNDS, STMT_LEN>>,
}

impl<A: StepApp + Clone, const ROUNDS: usize, const STMT_LEN: usize>
    CompiledBaseCase<A, ROUNDS, STMT_LEN>
where
    A::Witness: Clone,
{
    pub fn compile(app: A, witness: A::Witness) -> Self {
        use ark_ec::{AffineRepr, CurveGroup};
        let generator = Pallas::generator().into_group();
        let bootstrap_points = (1..=28u64)
            .map(|i| {
                let point = (generator * Fq::from(i)).into_affine();
                (point.x, point.y)
            })
            .collect();
        let (step_prover, step_verifier, wrap_prover, wrap_verifier) =
            match build_base_case::<A, ROUNDS, STMT_LEN>(
                app.clone(),
                witness,
                bootstrap_points,
                false,
                None,
                None,
                None,
                None,
            ) {
                BaseCaseBuild::Compiled {
                    step_prover,
                    step_verifier,
                    wrap_prover,
                    wrap_verifier,
                } => (step_prover, step_verifier, wrap_prover, wrap_verifier),
                BaseCaseBuild::Proof { .. } => unreachable!("compile mode returns indexes"),
            };
        // The bootstrap Wrap VK points only feed the Step proof's private
        // witness and public digest. They do not alter either circuit's
        // constraints, so the Wrap index produced by this discovery pass is
        // already the final fixed-point index. Recompiling it with its own VK
        // points used to create the exact same index a second time.
        let wrap_vk_pts = wrap_verification_key_points(&wrap_verifier);
        Self {
            app,
            wrap_vk_pts,
            step_indexes: Some((step_prover, step_verifier)),
            wrap_indexes: Some((wrap_prover, wrap_verifier)),
        }
    }

    /// Compiles the Step indexes alone, leaving the Wrap indexes empty.
    ///
    /// A branch of a shared program never uses a Wrap index of its own: the
    /// program builds ONE shared Wrap from every branch's Step verifier, and
    /// both the verification key and `prove_keep` read that shared index.
    /// Compiling a per-branch Wrap only to drop it costs most of the
    /// per-branch compile time, so a program compiles its branches this way.
    ///
    /// The resulting case cannot prove on its own; only a program that owns a
    /// shared Wrap can drive it.
    pub fn compile_step_only(app: A) -> Self {
        Self {
            step_indexes: Some(build_step_indexes::<A>(app.clone())),
            app,
            wrap_vk_pts: Vec::new(),
            wrap_indexes: None,
        }
    }

    pub fn prove(&mut self, witness: A::Witness) -> BaseCaseProof<A, ROUNDS, STMT_LEN> {
        let step_indexes = self.step_indexes.take().expect("compiled Step indexes");
        let wrap_indexes = self.wrap_indexes.take().expect("compiled Wrap indexes");
        match build_base_case::<A, ROUNDS, STMT_LEN>(
            self.app.clone(),
            witness,
            self.wrap_vk_pts.clone(),
            true,
            Some(step_indexes),
            Some(wrap_indexes),
            None,
            None,
        ) {
            BaseCaseBuild::Proof {
                proof,
                step_indexes,
                wrap_indexes,
                ..
            } => {
                self.step_indexes = Some(step_indexes);
                self.wrap_indexes = Some(wrap_indexes);
                proof
            }
            BaseCaseBuild::Compiled { .. } => unreachable!("proof mode returns a proof"),
        }
    }
}

/// [`prove_base_case`], additionally returning the compiled wrap circuit's
/// gates for parity tooling.
pub fn prove_base_case_with_wrap_dump<A: StepApp, const ROUNDS: usize, const STMT_LEN: usize>(
    app: A,
    witness: A::Witness,
    wrap_vk_pts: Vec<(Fp, Fp)>,
) -> (BaseCaseProof<A, ROUNDS, STMT_LEN>, WrapCircuitDump) {
    match build_base_case(app, witness, wrap_vk_pts, true, None, None, None, None) {
        BaseCaseBuild::Proof { proof, dump, .. } => (proof, dump),
        BaseCaseBuild::Compiled { .. } => unreachable!("proof mode returns a complete proof"),
    }
}

/// The kimchi Step verifier index shape shared by every recorded branch.
pub(crate) type SharedStepVerifierIndex =
    kimchi::verifier_index::VerifierIndex<FULL_ROUNDS, Vesta, poly_commitment::ipa::SRS<Vesta>>;

/// Build the SHARED width-0 wrap verifier over EVERY branch's Step verifier,
/// as OCaml `Pickles.compile` does for a `max_proofs_verified = 0` program:
/// ONE wrap circuit bakes all branch step-domains/VKs (selected at prove time
/// by a witnessed `which_branch` one-hot), so the whole program has a single
/// canonical side-loaded verification key instead of one wrap VK per branch.
///
/// Only the wrap VK shape is produced — no step proof is needed — which is all
/// the compile-only zkApp milestone requires. The wrap constraint system, and
/// therefore its 28 verification-key commitments, depends solely on the set of
/// branch Step verifier indexes, not on any witness.
pub(crate) fn build_shared_base_wrap(
    step_verifiers: &[&SharedStepVerifierIndex],
) -> (
    snarky::api::ProverIndexWrapper<WrapCircuit<16, 40>>,
    snarky::api::VerifierIndexWrapper<WrapCircuit<16, 40>>,
) {
    use ark_ec::{AffineRepr, CurveGroup};
    assert!(
        !step_verifiers.is_empty(),
        "a compiled program has at least one branch"
    );
    let co = |p: &Vesta| (p.x, p.y);
    // One `WrapBranchData` per branch (its Step VK commitments + domain). The
    // wrap folds them through the `which_branch` one-hot.
    let branches: Vec<WrapBranchData> = step_verifiers
        .iter()
        .map(|svi| WrapBranchData::from_step_verifier(svi, 0))
        .collect();
    // The step public-input statement layout is shared by every branch (all
    // Steps expose the same public-input type); only the x_hat Lagrange
    // constants differ, per the branch's Step domain.
    let step_statement = vec![WrapStepStatementSlot::Packed {
        value: Fq::from(0u64),
        num_bits: 255,
    }];
    // One x_hat Lagrange constant set per branch, built with the SAME helper
    // the recursive shared-wrap path uses (so the base program's wrap matches
    // jsoo's per-slot construction rather than a hand-rolled single pair).
    let step_statement_lagranges: Vec<Vec<((Fq, Fq), (Fq, Fq))>> = step_verifiers
        .iter()
        .map(|svi| {
            crate::recursive_step::step_statement_lagranges_for_domain(
                svi.domain.log_size_of_group as u32,
                &step_statement,
            )
        })
        .collect();

    // Proof-shaped values stay dummy (they are witness-only). Branch-zero's
    // top-level Step VK fields keep the historical single-branch layout for
    // `which_branch = 0`; the baked constants come from `branches`.
    let svi0 = step_verifiers[0];
    let generator = Vesta::generator().into_group().into_affine();
    let point = (generator.x, generator.y);
    let dummy_wrap_chals = {
        let endo_wrap = <Pallas as KimchiCurve<FULL_ROUNDS>>::endos().1;
        let endo_step = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1;
        crate::dummy::pad_wrap_challenges::<Fq, Fp>(&[], endo_wrap, endo_step)
    };
    let wdata = WrapWitnessData {
        which_branch: 0,
        // Shared multi-branch wrap: the wrap structure must emit the lookup
        // verification of any branch that uses it, so carry the first branch's
        // lookup usage (all lookup branches share the same feature-flag shape;
        // per-branch commitment VALUES are selected from `branches`).
        lookup: branches.iter().find_map(|b| b.lookup.clone()),
        lookup_sorted: proof_lookup_commitments(&branches.iter().find_map(|b| b.lookup.clone())).0,
        lookup_aggreg: proof_lookup_commitments(&branches.iter().find_map(|b| b.lookup.clone())).1,
        lookup_runtime: proof_lookup_commitments(&branches.iter().find_map(|b| b.lookup.clone())).2,
        branches,
        step_domain_log2: svi0.domain.log_size_of_group as u8,
        step_vk_digest: svi0.digest::<VestaBase>(),
        generic: co(&svi0.generic_comm.chunks[0]),
        psm: co(&svi0.psm_comm.chunks[0]),
        complete_add: co(&svi0.complete_add_comm.chunks[0]),
        mul: co(&svi0.mul_comm.chunks[0]),
        emul: co(&svi0.emul_comm.chunks[0]),
        endomul_scalar: co(&svi0.endomul_scalar_comm.chunks[0]),
        coefficients: svi0
            .coefficients_comm
            .iter()
            .map(|c| co(&c.chunks[0]))
            .collect(),
        sigma_init: svi0.sigma_comm[..PERMUTS - 1]
            .iter()
            .map(|c| co(&c.chunks[0]))
            .collect(),
        sigma_last: vec![co(&svi0.sigma_comm[PERMUTS - 1].chunks[0])],
        w_comm: vec![point; COLUMNS],
        z_comm: point,
        t_comm: vec![point; 7],
        lr: vec![(point, point); crate::common::TICK_ROUNDS],
        delta: point,
        sg: point,
        z1_repr: Fq::from(0u64),
        z2_repr: Fq::from(0u64),
        sg_olds: vec![],
        unfinalized: vec![],
        step_statement,
        step_statement_lagranges,
        h: (svi0.srs().h.x, svi0.srs().h.y),
        new_acc_dummies: dummy_wrap_chals,
    };
    let circuit = WrapCircuit::<16, 40> { w: Some(wdata) };
    let (wrap_prover, wrap_verifier) = circuit
        .compile_to_indexes_with_domain_and_srs(0, Some(crate::common::TOCK_ROUNDS as u32))
        .unwrap();
    (wrap_prover, wrap_verifier)
}

/// Compiles a Step circuit to its prover and verifier indexes. Mina proves
/// over the full Tick SRS (2^16) regardless of the circuit's domain, so step
/// IPA proofs always have 16 rounds.
pub(crate) fn build_step_indexes<A: StepApp>(app: A) -> StepIndexes<A> {
    StepCircuit { app }
        .compile_to_indexes_with_domain_and_srs(0, Some(crate::common::TICK_ROUNDS as u32))
        .unwrap()
}

pub(crate) fn build_base_case<A: StepApp, const ROUNDS: usize, const STMT_LEN: usize>(
    app: A,
    witness: A::Witness,
    wrap_vk_pts: Vec<(Fp, Fp)>,
    prove_wrap: bool,
    step_indexes: Option<StepIndexes<A>>,
    wrap_indexes: Option<WrapIndexes<ROUNDS, STMT_LEN>>,
    cached_wrap_index: Option<RawWrapIndex>,
    shared_wrap: Option<SharedBaseWrapData>,
) -> BaseCaseBuild<A, ROUNDS, STMT_LEN> {
    assert_eq!(
        STMT_LEN,
        13 + ROUNDS + 11,
        "STMT_LEN mismatch (OCaml 40-slot layout)"
    );
    // ---- step proof ----
    let app_state = app.state(&witness);
    let (mut step_pi, step_ver) = match step_indexes {
        Some(indexes) => indexes,
        None => build_step_indexes(app),
    };
    let svi = &step_ver.index;

    // Compiling a program must not require a satisfying application witness.
    // The Wrap constraint shape depends only on the fixed proof dimensions
    // and Step index layout, not on a concrete Step proof. Build that shape
    // directly instead of proving a disposable (and potentially invalid)
    // application execution merely to obtain proof-shaped values.
    if !prove_wrap {
        use ark_ec::{AffineRepr, CurveGroup};
        let generator = Vesta::generator().into_group().into_affine();
        let point = (generator.x, generator.y);
        let co = |p: &Vesta| (p.x, p.y);
        let dummy_wrap_chals = {
            let endo_wrap = <Pallas as KimchiCurve<FULL_ROUNDS>>::endos().1;
            let endo_step = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1;
            crate::dummy::pad_wrap_challenges::<Fq, Fp>(&[], endo_wrap, endo_step)
        };
        let lgr = svi.srs().get_lagrange_basis(svi.domain);
        let l0 = lgr[0].chunks[0];
        let correction = crate::public_input::lagrange_correction(&l0, 255);
        drop(lgr);
        let wdata = WrapWitnessData {
            which_branch: 0,
            branches: vec![],
            step_domain_log2: svi.domain.log_size_of_group as u8,
            step_vk_digest: svi.digest::<VestaBase>(),
        lookup: LookupBranchData::from_step_verifier(svi),
        lookup_sorted: proof_lookup_commitments(&LookupBranchData::from_step_verifier(svi)).0,
        lookup_aggreg: proof_lookup_commitments(&LookupBranchData::from_step_verifier(svi)).1,
        lookup_runtime: proof_lookup_commitments(&LookupBranchData::from_step_verifier(svi)).2,
            generic: co(&svi.generic_comm.chunks[0]),
            psm: co(&svi.psm_comm.chunks[0]),
            complete_add: co(&svi.complete_add_comm.chunks[0]),
            mul: co(&svi.mul_comm.chunks[0]),
            emul: co(&svi.emul_comm.chunks[0]),
            endomul_scalar: co(&svi.endomul_scalar_comm.chunks[0]),
            coefficients: svi
                .coefficients_comm
                .iter()
                .map(|c| co(&c.chunks[0]))
                .collect(),
            sigma_init: svi.sigma_comm[..PERMUTS - 1]
                .iter()
                .map(|c| co(&c.chunks[0]))
                .collect(),
            sigma_last: vec![co(&svi.sigma_comm[PERMUTS - 1].chunks[0])],
            w_comm: vec![point; COLUMNS],
            z_comm: point,
            // Kimchi's quotient commitment has seven chunks when the Step
            // index uses the full Tick SRS (one max-sized polynomial chunk).
            t_comm: vec![point; 7],
            lr: vec![(point, point); crate::common::TICK_ROUNDS],
            delta: point,
            sg: point,
            z1_repr: Fq::from(0u64),
            z2_repr: Fq::from(0u64),
            sg_olds: vec![],
            unfinalized: vec![],
            step_statement: vec![WrapStepStatementSlot::Packed {
                value: Fq::from(0u64),
                num_bits: 255,
            }],
            step_statement_lagranges: vec![vec![(co(&l0), co(&correction))]],
            h: (svi.srs().h.x, svi.srs().h.y),
            new_acc_dummies: dummy_wrap_chals,
        };
        let circuit = WrapCircuit::<ROUNDS, STMT_LEN> {
            w: Some(wdata.clone()),
        };
        let (wrap_prover, wrap_verifier) = match wrap_indexes {
            Some(indexes) => indexes,
            None => match cached_wrap_index {
                Some(index) => {
                    snarky::api::ProverIndexWrapper::from_cached_index(circuit, 0, index)
                        .unwrap_or_else(|_| {
                            WrapCircuit::<ROUNDS, STMT_LEN> { w: Some(wdata) }
                                .compile_to_indexes_with_domain_and_srs(
                                    0,
                                    Some(crate::common::TOCK_ROUNDS as u32),
                                )
                                .unwrap()
                        })
                }
                None => circuit
                    .compile_to_indexes_with_domain_and_srs(
                        0,
                        Some(crate::common::TOCK_ROUNDS as u32),
                    )
                    .unwrap(),
            },
        };
        return BaseCaseBuild::Compiled {
            step_prover: step_pi,
            step_verifier: step_ver,
            wrap_prover,
            wrap_verifier,
        };
    }

    let digest = crate::hash_messages::hash_messages_for_next_step_proof_ref(
        Vesta::sponge_params(),
        &wrap_vk_pts,
        &app_state,
        &[],
        &[],
    );
    // OCaml base-case step proofs carry NO kimchi-level recursion
    // challenges (`Max_proofs_verified = 0` for a 0-arity o1js rule): the
    // accumulator padding of `Wrap_hack` lives only inside the message
    // HASHES, never in the proof's `prev_challenges` — so the wrap circuit
    // has an EMPTY sg_old vector (nothing absorbed, nothing combined).
    let (step_proof, _) = step_pi
        .prove_with_recursion_mask::<VestaBase, VestaScalar>(
            digest,
            (witness, wrap_vk_pts.clone()),
            true,
            vec![],
            Some(&[]),
        )
        .unwrap();

    // ---- wrap witness ----
    let public_input = vec![digest];
    let lgr = svi.srs().get_lagrange_basis(svi.domain);
    let com: Vec<_> = lgr.iter().take(svi.public).collect();
    let elm: Vec<_> = public_input.iter().map(|s| -*s).collect();
    let pc = PolyComm::<Vesta>::multi_scalar_mul(&com, &elm);
    let public_comm = svi
        .srs()
        .mask_custom(pc.clone(), &pc.map(|_| Fp::one()))
        .unwrap()
        .commitment;
    let o = step_proof
        .oracles_with_recursion_mask::<VestaBase, VestaScalar, _>(
            svi,
            &public_comm,
            Some(&public_input),
            Some(&[]),
        )
        .unwrap();
    let oracles = &o.oracles;

    let combined = step_proof
        .evals
        .combine(&o.powers_of_eval_points_for_chunks);
    let srs_log2 = u64::BITS - 1 - (svi.max_poly_size as u64).leading_zeros();
    let domain = crate::plonk_checks::Domain::<Fp> {
        log2_size: svi.domain.log_size_of_group,
        generator: svi.domain.group_gen,
    };
    let selected_lookup = LookupBranchData::from_step_verifier(svi);
    let selected_features = plonk_features_from_lookup(&selected_lookup);
    let minimal = plonk::Minimal::<Fp, Fp, bool> {
        alpha: oracles.alpha,
        beta: oracles.beta,
        gamma: oracles.gamma,
        zeta: oracles.zeta,
        joint_combiner: oracles.joint_combiner.as_ref().map(|(_, field)| *field),
        feature_flags: selected_features,
    };
    let env = crate::plonk_checks::scalars_env::<Fp, bool>(&domain, srs_log2, &minimal);
    let evals = crate::plonk_checks::Evals {
        w: combined.w.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
        s: combined.s.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
        z: (combined.z.zeta, combined.z.zeta_omega),
    };
    let perm = crate::plonk_checks::perm_scalar(&env, &evals);

    let sg_old_points: Vec<Vesta> = step_proof
        .prev_challenges
        .iter()
        .map(|rc| rc.comm.chunks[0])
        .collect();
    let ww = crate::wrap::wrap_witness(
        svi.max_poly_size as u64,
        svi.domain.size,
        svi.domain.group_gen,
        &step_proof,
        &public_comm,
        svi.digest::<VestaBase>(),
        selected_lookup
            .as_ref()
            .is_some_and(|lookup| lookup.joint_lookup_used),
        &sg_old_points,
        None,
        o.combined_inner_product,
        oracles.zeta,
        oracles.u,
        perm,
    );
    assert_eq!(
        ww.sponge_digest, o.digest,
        "host wrap transcript must match kimchi's pre-evaluations digest"
    );

    let claimed_xi_raw: Fp = {
        use kimchi::plonk_sponge::FrSponge as _;
        let params = Vesta::sponge_params();
        let mut fr = VestaScalar::from(params);
        fr.absorb(&o.digest);
        let pcd = {
            let prev_sponge = VestaScalar::from(params);
            for rc in &step_proof.prev_challenges {
                let _ = rc; // empty in the base case (no kimchi recursion)
            }
            prev_sponge.digest()
        };
        fr.absorb(&pcd);
        fr.absorb(&step_proof.ft_eval1);
        fr.absorb_multiple(&o.public_evals[0]);
        fr.absorb_multiple(&o.public_evals[1]);
        fr.absorb_evaluations(&step_proof.evals);
        fr.squeeze(mina_poseidon::sponge::CHALLENGE_LENGTH_IN_LIMBS)
    };

    // ---- statement ----
    let dummy_wrap_chals: Vec<Vec<Fq>> = {
        let endo_wrap = <Pallas as KimchiCurve<FULL_ROUNDS>>::endos().1;
        let endo_step = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1;
        crate::dummy::pad_wrap_challenges::<Fq, Fp>(&[], endo_wrap, endo_step)
    };
    let dummy_wrap_raw_chals: Vec<Vec<Fq>> = {
        vec![
            crate::dummy::pasta_ipa_wrap_and_step()
                .0
                .prechallenges
                .clone();
            crate::common::MAX_PROOFS_VERIFIED
        ]
    };
    let sg_pt = step_proof.proof.sg;
    let msgs_wrap_digest = crate::hash_messages::hash_messages_for_next_wrap_proof_ref(
        Pallas::sponge_params(),
        &dummy_wrap_chals,
        &[],
        (sg_pt.x, sg_pt.y),
    );

    let plonk_vals = plonk::InCircuit::<Fq, ScalarChallenge<Fq>, bool> {
        alpha: ScalarChallenge(ww.alpha_raw),
        beta: ww.beta_raw,
        gamma: ww.gamma_raw,
        zeta: ScalarChallenge(ww.zeta_raw),
        zeta_to_srs_length: fp_to_fq(ww.zeta_to_srs_length_repr),
        zeta_to_domain_size: fp_to_fq(ww.zeta_to_domain_size_repr),
        perm: fp_to_fq(ww.perm_repr),
        feature_flags: selected_features,
        joint_combiner: oracles
            .joint_combiner
            .as_ref()
            .map(|(raw, _)| ScalarChallenge(fp_to_fq(raw.inner()))),
    };
    let bp_chals: Vec<BulletproofChallenge<ScalarChallenge<Fq>>> = ww
        .bulletproof_prechallenges
        .iter()
        .map(|&c| BulletproofChallenge {
            prechallenge: ScalarChallenge(c),
        })
        .collect();
    let branch = BranchData {
        proofs_verified: ProofsVerified::N0,
        domain_log2: svi.domain.log_size_of_group as u8,
    };
    let statement = crate::composition_types::wrap::wrap_statement_to_field_elements_ocaml(
        &plonk_vals,
        fp_to_fq(ww.cip_repr),
        fp_to_fq(ww.b_repr),
        &ScalarChallenge(fp_to_fq(claimed_xi_raw)),
        &bp_chals,
        &ScalarChallenge(Fq::from(0u64)),
        &branch,
        fp_to_fq(ww.sponge_digest),
        msgs_wrap_digest,
        fp_to_fq(digest),
    );
    assert_eq!(statement.len(), STMT_LEN, "statement length");
    let stable_statement = crate::mina_bin_prot::WrapStatementMinimalV1::from_flattened(
        statement.clone(),
        crate::mina_bin_prot::WrapMessagesForNextWrapProofV1 {
            challenge_polynomial_commitment: (sg_pt.x, sg_pt.y),
            old_bulletproof_challenges: dummy_wrap_raw_chals,
        },
        crate::mina_bin_prot::StepMessagesForNextProofV1 {
            challenge_polynomial_commitments: Vec::new(),
            old_bulletproof_challenges: Vec::new(),
        },
    )
    .unwrap();

    // ---- wrap proof ----
    let co = |p: &Vesta| (p.x, p.y);
    let l0 = lgr[0].chunks[0];
    let correction = crate::public_input::lagrange_correction(&l0, 255);
    drop(lgr); // release the SRS cache guard so step_ver can move below
    let srs_h = svi.srs().h;
    // One in-circuit sg_old per REAL kimchi recursion challenge — empty in
    // the base case, exactly as OCaml's `Max_proofs_verified = 0`.
    let physical_sg_olds: Vec<(Fq, Fq)> = step_proof
        .prev_challenges
        .iter()
        .map(|rc| co(&rc.comm.chunks[0]))
        .collect();
    let mut wdata = WrapWitnessData {
        which_branch: 0,
        branches: vec![],
        step_domain_log2: svi.domain.log_size_of_group as u8,
        step_vk_digest: svi.digest::<VestaBase>(),
        lookup: selected_lookup,
        lookup_sorted: step_proof
            .commitments
            .lookup
            .as_ref()
            .map(|lookup| lookup.sorted.iter().map(|c| co(&c.chunks[0])).collect())
            .unwrap_or_default(),
        lookup_aggreg: step_proof
            .commitments
            .lookup
            .as_ref()
            .map(|lookup| co(&lookup.aggreg.chunks[0]))
            .unwrap_or((Fq::from(0u64), Fq::from(0u64))),
        lookup_runtime: step_proof
            .commitments
            .lookup
            .as_ref()
            .and_then(|lookup| lookup.runtime.as_ref())
            .map(|runtime| co(&runtime.chunks[0])),
        generic: co(&svi.generic_comm.chunks[0]),
        psm: co(&svi.psm_comm.chunks[0]),
        complete_add: co(&svi.complete_add_comm.chunks[0]),
        mul: co(&svi.mul_comm.chunks[0]),
        emul: co(&svi.emul_comm.chunks[0]),
        endomul_scalar: co(&svi.endomul_scalar_comm.chunks[0]),
        coefficients: svi
            .coefficients_comm
            .iter()
            .map(|c| co(&c.chunks[0]))
            .collect(),
        sigma_init: svi.sigma_comm[..PERMUTS - 1]
            .iter()
            .map(|c| co(&c.chunks[0]))
            .collect(),
        sigma_last: vec![co(&svi.sigma_comm[PERMUTS - 1].chunks[0])],
        w_comm: step_proof
            .commitments
            .w_comm
            .iter()
            .map(|c| co(&c.chunks[0]))
            .collect(),
        z_comm: co(&step_proof.commitments.z_comm.chunks[0]),
        t_comm: step_proof
            .commitments
            .t_comm
            .chunks
            .iter()
            .map(co)
            .collect(),
        lr: step_proof
            .proof
            .lr
            .iter()
            .map(|(l, r)| (co(l), co(r)))
            .collect(),
        delta: co(&step_proof.proof.delta),
        sg: co(&sg_pt),
        z1_repr: fp_to_fq(ww.z1_repr),
        z2_repr: fp_to_fq(ww.z2_repr),
        sg_olds: physical_sg_olds,
        unfinalized: vec![],
        step_statement: vec![WrapStepStatementSlot::Packed {
            value: fp_to_fq(digest),
            num_bits: 255,
        }],
        step_statement_lagranges: vec![vec![(co(&l0), co(&correction))]],
        h: (srs_h.x, srs_h.y),
        new_acc_dummies: dummy_wrap_chals.clone(),
    };
    if let Some(shared) = shared_wrap {
        // A mixed program has one fixed Wrap circuit. OCaml's `Opt.Maybe`
        // keeps the lookup payload in that circuit even when the selected
        // branch does not use lookups; its public presence flag masks dummy
        // values. Keep the same structural payload here so witness generation
        // consumes exactly the variables compiled into the shared Wrap index.
        let structural_lookup = shared
            .branches
            .iter()
            .find_map(|branch| branch.lookup.clone());
        let selected_uses_lookup = wdata.lookup.is_some();
        wdata.which_branch = shared.which_branch;
        wdata.branches = shared.branches;
        wdata.step_statement_lagranges = shared.step_statement_lagranges;
        if !selected_uses_lookup {
            if let Some(shape) = structural_lookup {
                use ark_ec::{AffineRepr as _, CurveGroup as _};
                let generator = Vesta::generator().into_group().into_affine();
                let dummy = (generator.x, generator.y);
                wdata.lookup_sorted = vec![dummy; shape.sorted_count()];
                wdata.lookup_aggreg = dummy;
                wdata.lookup_runtime = shape.uses_runtime_tables.then_some(dummy);
                wdata.lookup = Some(shape);
            }
        }
    }

    let stmt_arr: [Fq; STMT_LEN] = statement
        .clone()
        .try_into()
        .unwrap_or_else(|_| unreachable!());
    // Full Tock SRS (2^15): wrap IPA proofs always have 15 rounds.
    let (mut wrap_pi, wrap_ver) = match wrap_indexes {
        Some(indexes) => indexes,
        None => {
            let circuit = WrapCircuit::<ROUNDS, STMT_LEN> {
                w: Some(wdata.clone()),
            };
            match cached_wrap_index {
                Some(index) => {
                    match snarky::api::ProverIndexWrapper::from_cached_index(circuit, 0, index) {
                        Ok(indexes) => indexes,
                        Err(_) => WrapCircuit::<ROUNDS, STMT_LEN> {
                            w: Some(wdata.clone()),
                        }
                        .compile_to_indexes_with_domain_and_srs(
                            0,
                            Some(crate::common::TOCK_ROUNDS as u32),
                        )
                        .unwrap(),
                    }
                }
                None => circuit
                    .compile_to_indexes_with_domain_and_srs(
                        0,
                        Some(crate::common::TOCK_ROUNDS as u32),
                    )
                    .unwrap(),
            }
        }
    };
    if !prove_wrap {
        return BaseCaseBuild::Compiled {
            step_prover: step_pi,
            step_verifier: step_ver,
            wrap_prover: wrap_pi,
            wrap_verifier: wrap_ver,
        };
    }
    let wrap_dump = WrapCircuitDump {
        public_input_size: wrap_pi.index.cs.public,
        gates: wrap_pi.index.cs.gates.to_vec(),
        labels: wrap_pi.gate_labels().to_vec(),
    };
    let dummy_wrap_sg = crate::dummy::pasta_dummy_wrap_sg();
    let wrap_recursions = dummy_wrap_chals
        .iter()
        .map(|challenges| kimchi::proof::RecursionChallenge {
            chals: challenges.clone(),
            comm: PolyComm {
                chunks: vec![dummy_wrap_sg],
            },
        })
        .collect();
    let (wrap_proof, _) = wrap_pi
        .prove_with_recursion::<PallasBase, PallasScalar>(stmt_arr, wdata, true, wrap_recursions)
        .unwrap();
    wrap_ver.verify::<PallasBase, PallasScalar>(wrap_proof.clone(), stmt_arr, ());

    BaseCaseBuild::Proof {
        proof: BaseCaseProof {
            statement,
            stable_statement,
            proof: wrap_proof,
            step_proof,
            step_verifier: step_ver.clone(),
            wrap_verifier: wrap_ver.clone(),
            wrap_vk_pts,
        },
        dump: wrap_dump,
        step_indexes: (step_pi, step_ver),
        wrap_indexes: (wrap_pi, wrap_ver),
    }
}
