//! In-circuit `ft_eval0` and its scalar environment
//! (the circuit counterpart of [crate::plonk_checks], used by
//! `finalize_other_proof`).
//!
//! The linearization constant term is evaluated with [crate::expr_eval] (the
//! in-circuit PolishToken interpreter); everything else is plain FieldVar
//! arithmetic threading the RunState.

use std::borrow::Cow;

use ark_ff::PrimeField;
use ark_poly::Radix2EvaluationDomain as D;

use snarky::{Boolean, FieldVar, RunState, SnarkyResult};

use crate::expr_eval::pow_circuit;

/// The step-proof evaluation domain used by `finalize_other_proof`.
///
/// `Fixed` is the historical constant path (single known domain baked into
/// the circuit). `Selected` is the port of OCaml's
/// `Step_verifier.domain_for_compiled` + `Pseudo.Domain`: the previous
/// proof's `branch_data.domain_log2` (a witness) one-hot selects among the
/// program's unique per-branch step domains, so one compiled circuit
/// finalizes proofs from branches with different natural domains.
#[derive(Clone)]
pub enum FinalizeDomain<F: PrimeField> {
    Fixed(D<F>),
    Selected(SelectedDomain<F>),
    /// Deferred [`SelectedDomain`]: `finalize_deferred` materializes the
    /// one-hot at OCaml's `domain_for_compiled` position (Step 3, between the
    /// plonk scalar conversions and the `zetaw` multiply) so the equality
    /// gadgets land on the same rows.
    SelectFrom {
        log2s: Vec<u32>,
        domain_log2: FieldVar<F>,
    },
    /// Deferred [`SideLoadedDomain`]: a side-loaded slot's finalize domain
    /// comes from the WITNESSED `branch_data.domain_log2` over the full
    /// permissible range (OCaml `Step_verifier.side_loaded_domain`, max =
    /// Tick rounds).
    SideLoadedFrom { log2_size: FieldVar<F> },
    SideLoadedSelected(SideLoadedDomain<F>),
}

/// OCaml `Step_verifier.side_loaded_domain` (step_verifier.ml:719-742): the
/// domain of a side-loaded proof, from a witnessed `log2_size` in
/// `0..=max` (max = Tick rounds = 16): a ones-prefix mask drives the masked
/// squaring chain of the vanishing polynomial, and a one-hot selects the
/// generator constant.
#[derive(Clone)]
pub struct SideLoadedDomain<F: PrimeField> {
    pub mask: Vec<Boolean<F>>,
    pub which: Vec<Boolean<F>>,
}

pub const SIDE_LOADED_MAX_DOMAIN_LOG2: usize = 16;

impl<F: PrimeField> SideLoadedDomain<F> {
    /// Emits `ones_vector ~first_zero:log2_size` (util.ml:51) then
    /// `One_hot.of_index log2_size ~length:(max+1)` (one_hot_vector.ml)
    /// with its `Boolean.Assert.any`, in OCaml's order.
    pub fn create(
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        log2_size: &FieldVar<F>,
    ) -> SnarkyResult<Self> {
        let max = SIDE_LOADED_MAX_DOMAIN_LOG2;
        // ones_vector: value_i = value_{i-1} AND NOT (log2_size == i)
        let mut mask = Vec::with_capacity(max);
        let mut value = Boolean::true_();
        for i in 0..max {
            // `Field.equal first_zero (of_int i)` — the WITNESS is the left
            // operand (operand order decides the equal gadget's coefficient
            // signs).
            let eq = log2_size
                .clone()
                .equal(sys, loc.clone(), &FieldVar::constant(F::from(i as u64)))?;
            value = value.and(&eq.not(), sys, loc.clone());
            mask.push(value.clone());
        }
        // of_index: b_j = (j == log2_size), then Assert.any = assert_non_zero
        // of the boolean sum (utils.ml:361 — inverse witness + one r1cs).
        let mut which = Vec::with_capacity(max + 1);
        for j in 0..=max {
            which.push(FieldVar::constant(F::from(j as u64)).equal(sys, loc.clone(), log2_size)?);
        }
        let fields: Vec<FieldVar<F>> = which.iter().map(|b| b.to_field_var()).collect();
        let sum = FieldVar::sum(&fields.iter().collect::<Vec<_>>());
        let sum_for_witness = sum.clone();
        let sum_inv: FieldVar<F> = sys.compute(loc.clone(), move |env| {
            use ark_ff::Field as _;
            env.read_var(&sum_for_witness)
                .inverse()
                .unwrap_or_else(F::zero)
        })?;
        sys.assert_r1cs(
            Some("side-loaded domain one-hot any".into()),
            loc,
            sum,
            sum_inv,
            FieldVar::constant(F::one()),
        )?;
        Ok(Self { mask, which })
    }

    /// `Pseudo.Domain.generator` over the one-hot: a constants mask
    /// (no rows).
    pub fn generator_var(&self) -> FieldVar<F>
    where
        F: ark_ff::FftField,
    {
        let mut acc = FieldVar::constant(F::zero());
        for (j, b) in self.which.iter().enumerate() {
            let gen = if j == 0 {
                F::one()
            } else {
                SelectedDomain::<F>::generator_of(j as u32)
            };
            acc = &acc + &b.to_field_var().scale(gen);
        }
        acc
    }

    /// The masked squaring chain (step_verifier.ml:698-712):
    /// `fold i: acc = if mask[i] then acc² else acc`, minus one. No seal.
    pub fn vanishing_polynomial(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        x: &FieldVar<F>,
    ) -> SnarkyResult<FieldVar<F>> {
        let mut acc = x.clone();
        for bit in &self.mask {
            let squared = crate::expr_eval::square_circuit(sys, loc.clone(), &acc)?;
            let selected = sys.if_(loc.clone(), bit.clone(), squared, acc)?;
            acc = selected;
        }
        Ok(&acc - &FieldVar::constant(F::one()))
    }
}

/// The one-hot-selected pseudo domain (OCaml `Pseudo.Domain`).
#[derive(Clone)]
pub struct SelectedDomain<F: PrimeField> {
    /// Unique, sorted `log2` sizes of the program's branch step domains.
    pub log2s: Vec<u32>,
    /// `which[i] = (branch_data.domain_log2 == log2s[i])`, from the witness.
    pub which: Vec<Boolean<F>>,
}

impl<F: PrimeField> SelectedDomain<F> {
    /// One-hot over the unique domain list from the (witness) `domain_log2`
    /// variable — OCaml `domain_for_compiled`'s `which_log2`.
    pub fn create(
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        log2s: &[u32],
        domain_log2: &FieldVar<F>,
    ) -> SnarkyResult<Self> {
        // OCaml `domain_for_compiled` builds the one-hot with `Vector.map`,
        // whose `f` runs from the LAST element to the FIRST (right-to-left, the
        // same evaluation order behind the api.rs `choose_pts` `.rev()`). So the
        // equality bit for the LARGEST log2 is allocated first (smallest
        // variable index). `reduce_lincom` later orders terms by ascending
        // variable index, so this decides how the masked-generator lincom
        // `Σ which[i]·ω_i` pairs its domain generators when multiplied by zeta.
        // Allocating left-to-right swaps that pairing (`finalize | zetaw` and
        // `| env` half-gates diverge from jsoo). Emit right-to-left, keeping
        // `which[i]` paired with `log2s[i]`.
        let mut which: Vec<Option<Boolean<F>>> = (0..log2s.len()).map(|_| None).collect();
        for (i, &l) in log2s.iter().enumerate().rev() {
            which[i] =
                Some(FieldVar::constant(F::from(u64::from(l))).equal(sys, loc.clone(), domain_log2)?);
        }
        let which = which.into_iter().map(|b| b.expect("all set")).collect();
        Ok(Self {
            log2s: log2s.to_vec(),
            which,
        })
    }

    /// The domain generator for a `log2`-sized radix-2 domain.
    pub fn generator_of(log2: u32) -> F
    where
        F: ark_ff::FftField,
    {
        use ark_poly::EvaluationDomain;
        D::<F>::new(1usize << log2)
            .expect("radix-2 domain")
            .group_gen
    }

    /// OCaml `Pseudo.mask`: `Σ which[i] · constants[i]` — a pure linear
    /// combination (no constraints).
    pub fn mask_constants(&self, constants: &[F]) -> FieldVar<F> {
        assert_eq!(constants.len(), self.which.len());
        let mut acc = FieldVar::constant(F::zero());
        for (b, &c) in self.which.iter().zip(constants) {
            acc = &acc + &b.to_field_var().scale(c);
        }
        acc
    }

    /// OCaml `Pseudo.mask` over variables: `Σ which[i] · xs[i]`.
    pub fn mask_vars(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        xs: &[FieldVar<F>],
    ) -> SnarkyResult<FieldVar<F>> {
        assert_eq!(xs.len(), self.which.len());
        // OCaml `Pseudo.mask` builds the products with `Vector.map`, so their
        // constraints are emitted from the last vector element to the first.
        // The resulting vector is still folded in logical order.
        let mut terms: Vec<Option<FieldVar<F>>> = (0..xs.len()).map(|_| None).collect();
        for i in (0..xs.len()).rev() {
            terms[i] = Some(
                self.which[i]
                    .to_field_var()
                    .mul(&xs[i], None, loc.clone(), sys)?,
            );
        }
        let mut acc = FieldVar::constant(F::zero());
        for term in terms {
            acc = &acc + &term.expect("all pseudo-mask terms set");
        }
        Ok(acc)
    }

    /// The masked generator `Σ which[i] · ω_i` (constants ⇒ no constraints).
    pub fn generator_var(&self) -> FieldVar<F>
    where
        F: ark_ff::FftField,
    {
        let gens: Vec<F> = self.log2s.iter().map(|&l| Self::generator_of(l)).collect();
        self.mask_constants(&gens)
    }

    /// OCaml `Pseudo.Domain.to_domain`'s `vanishing_polynomial x`:
    /// `seal(choose(x^{2^log2_i}) - 1)` via a squaring chain to the largest
    /// listed domain.
    pub fn vanishing_polynomial(
        &self,
        sys: &mut RunState<F>,
        loc: Cow<'static, str>,
        x: &FieldVar<F>,
    ) -> SnarkyResult<FieldVar<F>>
    where
        F: ark_ff::FftField,
    {
        let max_log2 = *self.log2s.iter().max().expect("non-empty domain list");
        let mut pow2_pows = vec![x.clone()];
        for i in 1..=max_log2 as usize {
            let prev = pow2_pows[i - 1].clone();
            // OCaml `Pseudo.Domain.vanishing_polynomial` squares with
            // `Field.square` (pseudo.ml:118) — a Square constraint.
            pow2_pows.push(crate::expr_eval::square_circuit(sys, loc.clone(), &prev)?);
        }
        let picks: Vec<FieldVar<F>> = self
            .log2s
            .iter()
            .map(|&l| pow2_pows[l as usize].clone())
            .collect();
        let chosen = self.mask_vars(sys, loc.clone(), &picks)?;
        (&chosen - &FieldVar::constant(F::one())).seal(sys, loc)
    }
}

/// The precomputed `ω^{-k}` values of the finalize domain: constants on the
/// `Fixed` path, circuit variables (division from the masked generator, as
/// in OCaml `Plonk_checks.scalars_env`) on the `Selected` path.
#[derive(Clone)]
pub struct DomainOmegas<F: PrimeField> {
    pub generator: FieldVar<F>,
    pub omega_to_minus_1: FieldVar<F>,
    /// `ω^{-2}` (`omega_to_zk_plus_1` for `zk_rows = 3`).
    pub omega_to_zk_plus_1: FieldVar<F>,
    /// `ω^{-3}` (`omega_to_zk` for `zk_rows = 3`).
    pub omega_to_zk: FieldVar<F>,
}

/// The scalars environment as circuit variables (mirror of
/// [crate::plonk_checks::ScalarsEnv]).
pub struct ScalarsEnvVar<F: PrimeField> {
    pub alpha_pows: Vec<FieldVar<F>>,
    pub zk_polynomial: FieldVar<F>,
    pub omega_to_minus_zk_rows: FieldVar<F>,
    pub zeta_to_n_minus_1: FieldVar<F>,
    /// `zeta_to_srs_length` is LAZY in OCaml (plonk_checks.ml:294) and its
    /// only in-circuit force site is the multi-chunk `p_eval0` fold of
    /// `ft_eval0` (:363-368) — with a single public-eval chunk the squaring
    /// chain is NEVER emitted (measured: no 16-square block anywhere in the
    /// jsoo finalize regions). Only the log2 is carried; the fold
    /// materializes the power on its first extra chunk.
    pub srs_length_log2: u32,
    pub beta: FieldVar<F>,
    pub gamma: FieldVar<F>,
    pub zeta: FieldVar<F>,
    /// The `ω^{-k}` chain, for the PolishToken evaluator's domain-dependent
    /// tokens.
    pub omegas: DomainOmegas<F>,
}

impl<F: PrimeField> ScalarsEnvVar<F> {
    pub fn alpha_pow(&self, i: usize) -> FieldVar<F> {
        self.alpha_pows[i].clone()
    }
}

/// Builds the in-circuit scalars environment from the challenge variables
/// `alpha`, `beta`, `gamma`, `zeta` (`zk_rows = 3`).
#[allow(clippy::too_many_arguments)]
pub fn scalars_env_circuit<F: PrimeField + ark_ff::FftField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    domain: &FinalizeDomain<F>,
    srs_length_log2: u32,
    alpha: &FieldVar<F>,
    beta: FieldVar<F>,
    gamma: FieldVar<F>,
    zeta: &FieldVar<F>,
) -> SnarkyResult<ScalarsEnvVar<F>> {
    use crate::plonk_checks::NUM_ALPHA_POWS;

    let mut alpha_pows = vec![FieldVar::constant(F::one()), alpha.clone()];
    for i in 2..NUM_ALPHA_POWS {
        let prev = alpha_pows[i - 1].clone();
        alpha_pows.push(alpha.mul(&prev, None, loc.clone(), sys)?);
    }

    // ω^{-k} chain: constants for a fixed known domain; for a pseudo domain,
    // variables derived by division from the masked generator, exactly as in
    // OCaml `Plonk_checks.scalars_env` (`one / gen`, then repeated products).
    let omegas = match domain {
        FinalizeDomain::Fixed(d) => {
            let omega_to_minus_1 = d.group_gen.inverse().unwrap();
            let omega_to_zk_plus_1 = omega_to_minus_1.square();
            let omega_to_zk = omega_to_zk_plus_1 * omega_to_minus_1;
            DomainOmegas {
                generator: FieldVar::constant(d.group_gen),
                omega_to_minus_1: FieldVar::constant(omega_to_minus_1),
                omega_to_zk_plus_1: FieldVar::constant(omega_to_zk_plus_1),
                omega_to_zk: FieldVar::constant(omega_to_zk),
            }
        }
        FinalizeDomain::Selected(sel) => {
            let generator = sel.generator_var();
            let one = FieldVar::constant(F::one());
            let omega_to_minus_1 =
                crate::plonk_curve_ops::div_snarky(sys, loc.clone(), &one, &generator)?;
            // OCaml: `omega_to_minus_2 = square omega_to_minus_1`
            // (plonk_checks.ml:250) with `square x = x * x` — a MUL gadget.
            let omega_to_zk_plus_1 =
                omega_to_minus_1.mul(&omega_to_minus_1, None, loc.clone(), sys)?;
            let omega_to_zk = omega_to_zk_plus_1.mul(&omega_to_minus_1, None, loc.clone(), sys)?;
            DomainOmegas {
                generator,
                omega_to_minus_1,
                omega_to_zk_plus_1,
                omega_to_zk,
            }
        }
        FinalizeDomain::SideLoadedSelected(sel) => {
            let generator = sel.generator_var();
            let one = FieldVar::constant(F::one());
            let omega_to_minus_1 =
                crate::plonk_curve_ops::div_snarky(sys, loc.clone(), &one, &generator)?;
            let omega_to_zk_plus_1 =
                omega_to_minus_1.mul(&omega_to_minus_1, None, loc.clone(), sys)?;
            let omega_to_zk = omega_to_zk_plus_1.mul(&omega_to_minus_1, None, loc.clone(), sys)?;
            DomainOmegas {
                generator,
                omega_to_minus_1,
                omega_to_zk_plus_1,
                omega_to_zk,
            }
        }
        FinalizeDomain::SelectFrom { .. } | FinalizeDomain::SideLoadedFrom { .. } => {
            unreachable!("scalars_env_circuit: SelectFrom is materialized by finalize_deferred")
        }
    };

    // zk_polynomial = (zeta - w^-1)(zeta - w^-2)(zeta - w^-3)
    let f1 = zeta - &omegas.omega_to_minus_1;
    let f2 = zeta - &omegas.omega_to_zk_plus_1;
    let f3 = zeta - &omegas.omega_to_zk;
    let f12 = f1.mul(&f2, None, loc.clone(), sys)?;
    let zk_polynomial = f12.mul(&f3, None, loc.clone(), sys)?;

    let zeta_to_n_minus_1 = match domain {
        FinalizeDomain::Fixed(d) => {
            let zeta_n = pow_circuit(sys, loc.clone(), zeta, d.size)?;
            &zeta_n - &FieldVar::constant(F::one())
        }
        FinalizeDomain::Selected(sel) => sel.vanishing_polynomial(sys, loc.clone(), zeta)?,
        FinalizeDomain::SideLoadedSelected(sel) => {
            sel.vanishing_polynomial(sys, loc.clone(), zeta)?
        }
        FinalizeDomain::SelectFrom { .. } | FinalizeDomain::SideLoadedFrom { .. } => {
            unreachable!("scalars_env_circuit: SelectFrom is materialized by finalize_deferred")
        }
    };
    Ok(ScalarsEnvVar {
        alpha_pows,
        zk_polynomial,
        omega_to_minus_zk_rows: omegas.omega_to_zk.clone(),
        zeta_to_n_minus_1,
        srs_length_log2,
        beta,
        gamma,
        zeta: zeta.clone(),
        omegas,
    })
}

/// The proof evaluations as circuit variables.
pub struct EvalsVar<F: PrimeField> {
    pub w: Vec<(FieldVar<F>, FieldVar<F>)>,
    pub s: Vec<(FieldVar<F>, FieldVar<F>)>,
    pub z: (FieldVar<F>, FieldVar<F>),
}

/// Combines a polynomial's chunked evaluations into a single value by Horner's
/// rule (pickles' `actual_evaluation`): for chunks `[e_0, .., e_{k-1}]` and
/// `pt_to_n = pt^n`, returns `e_0 + pt_to_n·e_1 + .. + pt_to_n^{k-1}·e_{k-1}`.
/// For a single chunk it is the identity.
pub fn actual_evaluation_circuit<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    chunks: &[FieldVar<F>],
    pt_to_n: &FieldVar<F>,
) -> SnarkyResult<FieldVar<F>> {
    let mut it = chunks.iter().rev();
    let mut acc = it.next().expect("empty evaluation chunks").clone();
    for y in it {
        let pt_acc = pt_to_n.mul(&acc, None, loc.clone(), sys)?;
        acc = y + &pt_acc;
    }
    Ok(acc)
}

/// In-circuit permutation scalar (mirror of
/// [crate::plonk_checks::perm_scalar] / the `perm` of pickles' `derive_plonk`):
/// `- z(zeta omega) * beta * alpha^21 * zkp * prod_i (gamma + beta s_i + w_i)`.
///
/// This is the only scalar checked by `Plonk_checks.checked`
/// (`plonk_checks_passed`): the caller compares it to the claimed `perm` of the
/// deferred statement.
pub fn perm_scalar_circuit<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    env: &ScalarsEnvVar<F>,
    e: &EvalsVar<F>,
) -> SnarkyResult<FieldVar<F>> {
    use crate::plonk_checks::PERM_ALPHA0;

    let a21 = env.alpha_pow(PERM_ALPHA0);
    // acc = z(zeta*omega) * beta * alpha^21 * zkp
    let t1 = e.z.1.mul(&env.beta, None, loc.clone(), sys)?;
    let t2 = t1.mul(&a21, None, loc.clone(), sys)?;
    let mut acc = t2.mul(&env.zk_polynomial, None, loc.clone(), sys)?;
    for (i, (s, _)) in e.s.iter().enumerate() {
        // factor = gamma + beta * s_i + w_i(zeta)
        let bs = env.beta.mul(s, None, loc.clone(), sys)?;
        let factor = &(&env.gamma + &bs) + &e.w[i].0;
        acc = acc.mul(&factor, None, loc.clone(), sys)?;
    }
    // OCaml `derive_plonk` keeps `negate(fold)` as an UNSEALED lincom
    // (plonk_checks.ml:427); the perm check's `Shifted_value.of_field` + `equal`
    // then reference the positive fold var at +1/2. Sealing the negated value
    // into a fresh var would flip the perm-check gate's derived coeff to -1/2
    // (measured vs jsoo's +1/2). Return the negate as a lincom.
    Ok(acc.scale(-F::one()))
}

/// In-circuit `ft_eval0` WITHOUT the trailing `- constant_term` (OCaml
/// computes `Sc.constant_term env` LAST, plonk_checks.ml:398-399; the caller
/// evaluates the linearization after this prefix and subtracts).
pub fn ft_eval0_prefix_circuit<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    env: &ScalarsEnvVar<F>,
    shifts: &[F],
    e: &EvalsVar<F>,
    p_eval0: &[FieldVar<F>],
) -> SnarkyResult<FieldVar<F>> {
    use crate::plonk_checks::PERM_ALPHA0;

    let zkp = &env.zk_polynomial;
    let zeta1m1 = &env.zeta_to_n_minus_1;
    let (beta, gamma, zeta) = (&env.beta, &env.gamma, &env.zeta);

    // combine public-eval chunks by powers of zeta^{srs_length} — OCaml's
    // `Array.fold_right` (plonk_checks.ml:361-368) forces the lazy
    // `zeta_to_srs_length` on its FIRST extra chunk, so the squaring chain
    // is emitted here (once), and not at all for single-chunk evals.
    let mut chunks = p_eval0.iter().rev();
    let mut p = chunks.next().expect("empty public evals").clone();
    let mut zeta1: Option<FieldVar<F>> = None;
    for chunk in chunks {
        let zeta1 = match &zeta1 {
            Some(z) => z.clone(),
            None => {
                let z = pow_circuit(sys, loc.clone(), zeta, 1u64 << env.srs_length_log2)?;
                zeta1 = Some(z.clone());
                z
            }
        };
        let scaled = zeta1.mul(&p, None, loc.clone(), sys)?;
        p = chunk + &scaled;
    }
    let p_eval0 = p;

    let w0: Vec<FieldVar<F>> = e.w.iter().map(|(z, _)| z.clone()).collect();

    // init = (w_n + gamma) * z1 * alpha^0 * zkp ; then fold the sigma terms
    let mut ft = {
        let a0 = env.alpha_pow(PERM_ALPHA0);
        let w_n = w0[e.s.len()].clone();
        let t1 = (&w_n + gamma).mul(&e.z.1, None, loc.clone(), sys)?;
        let t2 = t1.mul(&a0, None, loc.clone(), sys)?;
        let mut acc = t2.mul(zkp, None, loc.clone(), sys)?;
        for (i, (s, _)) in e.s.iter().enumerate() {
            // OCaml: `((beta * s) + w0.(i) + gamma) * acc` — factor LEFT.
            let bs = beta.mul(s, None, loc.clone(), sys)?;
            let factor = &(&bs + &w0[i]) + gamma;
            acc = factor.mul(&acc, None, loc.clone(), sys)?;
        }
        acc
    };

    ft = &ft - &p_eval0;

    // subtract the shift product term:
    // alpha^0 * zkp * z(zeta) * prod_i (gamma + beta*zeta*s_i + w0_i)
    let shift_loc: Cow<'static, str> = Cow::Owned(format!("{loc} | ft_shift"));
    ft = {
        let a0zkp = env
            .alpha_pow(PERM_ALPHA0)
            .mul(zkp, None, shift_loc.clone(), sys)?;
        let mut acc = a0zkp.mul(&e.z.0, None, shift_loc.clone(), sys)?;
        for (i, s) in shifts.iter().enumerate() {
            // OCaml: `acc * (gamma + (beta * zeta * s) + w0.(i))` — the
            // `beta * zeta` product is NOT hoisted (one mul per shift).
            let beta_zeta = beta.mul(zeta, None, shift_loc.clone(), sys)?;
            let bzs = beta_zeta.scale(*s);
            let factor = &(gamma + &bzs) + &w0[i];
            acc = acc.mul(&factor, None, shift_loc.clone(), sys)?;
        }
        &ft - &acc
    };

    // + numerator / denominator
    let nd: Cow<'static, str> = Cow::Owned(format!("{loc} | ft_numden"));
    let one = FieldVar::constant(F::one());
    let om_zk = env.omega_to_minus_zk_rows.clone();
    let zeta_minus_omzk = zeta - &om_zk;
    let zeta_minus_1 = zeta - &one;
    let a1 = env.alpha_pow(PERM_ALPHA0 + 1);
    let a2 = env.alpha_pow(PERM_ALPHA0 + 2);
    // OCaml `nominator = (t1 + t2) * (1 - e0 z)` (plonk_checks.ml:390s): the
    // `+`'s operands evaluate RIGHT-TO-LEFT, so the (zeta - 1) term's gates
    // are emitted before the (zeta - omega^{-zk}) term's.
    let term2 =
        zeta1m1
            .mul(&a2, None, nd.clone(), sys)?
            .mul(&zeta_minus_1, None, nd.clone(), sys)?;
    let term1 =
        zeta1m1
            .mul(&a1, None, nd.clone(), sys)?
            .mul(&zeta_minus_omzk, None, nd.clone(), sys)?;
    let one_minus_z0 = &one - &e.z.0;
    let numerator = (&term1 + &term2).mul(&one_minus_z0, None, nd.clone(), sys)?;
    let denominator = zeta_minus_omzk.mul(&zeta_minus_1, None, nd.clone(), sys)?;
    let frac = crate::plonk_curve_ops::div_snarky(sys, loc, &numerator, &denominator)?;
    ft = &ft + &frac;

    Ok(ft)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        expr_eval::{eval_polish, PolishEnv},
        plonk_checks::ZK_ROWS,
    };
    use ark_ff::{One, Zero};
    use kimchi::{
        circuits::{
            berkeley_columns::{BerkeleyChallengeTerm, Column},
            expr::{ColumnEvaluations, PolishToken},
            gate::CurrOrNext,
        },
        curve::KimchiCurve,
    };
    use mina_curves::pasta::{Fp, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::{commitment::PolyComm, ipa::OpeningProof, SRS};
    use snarky::{api::SnarkyCircuit, loc};
    use std::collections::HashMap;

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    struct SmallCircuit {}
    impl SnarkyCircuit for SmallCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = Fp;
        type PublicInput = FieldVar<Fp>;
        type PublicOutput = ();
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            z: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<()> {
            let x: FieldVar<Fp> = sys.compute(loc!(), |_| *private.unwrap())?;
            let xx = x.mul(&x, None, loc!(), sys)?;
            xx.assert_equals(sys, loc!(), &z)?;
            let _ = sys.poseidon(loc!(), (x, z));
            Ok(())
        }
    }

    /// Captured pieces of a real proof, replayed in the ft_eval0 circuit.
    struct FtCircuit {
        tokens: Vec<PolishToken<Fp, Column, BerkeleyChallengeTerm>>,
        domain: D<Fp>,
        srs_log2: u32,
        endo: Fp,
        shifts: Vec<Fp>,
        alpha: Fp,
        beta: Fp,
        gamma: Fp,
        zeta: Fp,
        w: Vec<(Fp, Fp)>,
        s: Vec<(Fp, Fp)>,
        zperm: (Fp, Fp),
        public_evals0: Vec<Fp>,
        col_vals: HashMap<(Column, bool), Fp>,
    }

    impl SnarkyCircuit for FtCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        // (ft_eval0, perm) — perm shares env/evals with ft_eval0
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>);

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            _private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<(FieldVar<Fp>, FieldVar<Fp>)> {
            let w = |sys: &mut RunState<Fp>, v: Fp| sys.compute(loc!(), move |_| v);
            let zeta = w(sys, self.zeta)?;
            let alpha = w(sys, self.alpha)?;
            let beta = w(sys, self.beta)?;
            let gamma = w(sys, self.gamma)?;

            // scalars env in-circuit
            let env = scalars_env_circuit(
                sys,
                loc!(),
                &FinalizeDomain::Fixed(self.domain),
                self.srs_log2,
                &alpha,
                beta.clone(),
                gamma.clone(),
                &zeta,
            )?;

            // witness evals
            let wpair = |sys: &mut RunState<Fp>,
                         p: (Fp, Fp)|
             -> SnarkyResult<(FieldVar<Fp>, FieldVar<Fp>)> {
                Ok((
                    sys.compute(loc!(), move |_| p.0)?,
                    sys.compute(loc!(), move |_| p.1)?,
                ))
            };
            let mut ew = vec![];
            for p in &self.w {
                ew.push(wpair(sys, *p)?);
            }
            let mut es = vec![];
            for p in &self.s {
                es.push(wpair(sys, *p)?);
            }
            let ez = wpair(sys, self.zperm)?;
            let evals = EvalsVar {
                w: ew,
                s: es,
                z: ez,
            };
            let mut p_eval0 = vec![];
            for v in &self.public_evals0 {
                p_eval0.push(w(sys, *v)?);
            }

            // constant term via the polish interpreter
            let mds = &Vesta::sponge_params().mds;
            let mds: Vec<Vec<Fp>> = mds.iter().map(|r| r.to_vec()).collect();
            let mut col_map: HashMap<(Column, bool), FieldVar<Fp>> = HashMap::new();
            for (&(col, is_next), &v) in &self.col_vals {
                col_map.insert((col, is_next), w(sys, v)?);
            }
            let challenge = |t: BerkeleyChallengeTerm| match t {
                BerkeleyChallengeTerm::Alpha => alpha.clone(),
                BerkeleyChallengeTerm::Beta => beta.clone(),
                BerkeleyChallengeTerm::Gamma => gamma.clone(),
                BerkeleyChallengeTerm::JointCombiner => FieldVar::constant(Fp::zero()),
            };
            let column = |col: Column, row: CurrOrNext| {
                col_map[&(col, matches!(row, CurrOrNext::Next))].clone()
            };
            let penv = PolishEnv {
                domain: crate::expr_eval::PolishDomain::Fixed(self.domain),
                endo_coefficient: self.endo,
                mds: &mds,
                zk_rows: ZK_ROWS as u64,
                pt: zeta.clone(),
                zk_polynomial: None,
                zeta_to_n_minus_1: None,
                challenge: &challenge,
                column: &column,
            };
            let constant_term = eval_polish(sys, loc!(), &self.tokens, &penv)?;

            let ft_prefix = ft_eval0_prefix_circuit(
                sys,
                loc!(),
                &env,
                &self.shifts,
                &evals,
                &p_eval0,
            )?;
            let ft0 = &ft_prefix - &constant_term;
            // This test wires `perm` as a circuit output, so seal the lincom to
            // a var here (the production perm check keeps it unsealed to match
            // OCaml's `Shifted_value.of_field` pairing).
            let perm = perm_scalar_circuit(sys, loc!(), &env, &evals)?.seal(sys, loc!())?;
            Ok((ft0, perm))
        }
    }

    /// In-circuit ft_eval0 equals kimchi's OraclesResult.ft_eval0.
    #[test]
    fn ft_eval0_circuit_matches_kimchi() {
        let mut pi = SmallCircuit {}.compile_to_indexes().unwrap().0;
        let vi = SmallCircuit {}.compile_to_indexes().unwrap().1;
        let vi = &vi.index;
        let x = Fp::from(6u64);
        let z = x * x;
        let (proof, _) = pi.prove::<BaseSponge, ScalarSponge>(z, x, true).unwrap();
        let public_input = vec![z];
        let lgr = vi.srs().get_lagrange_basis(vi.domain);
        let com: Vec<_> = lgr.iter().take(vi.public).collect();
        let elm: Vec<_> = public_input.iter().map(|s| -*s).collect();
        let pc = PolyComm::<Vesta>::multi_scalar_mul(&com, &elm);
        let public_comm = vi
            .srs()
            .mask_custom(pc.clone(), &pc.map(|_| Fp::one()))
            .unwrap()
            .commitment;
        let o = proof
            .oracles::<BaseSponge, ScalarSponge, _>(vi, &public_comm, Some(&public_input))
            .unwrap();
        let oracles = &o.oracles;
        let combined = proof.evals.combine(&o.powers_of_eval_points_for_chunks);

        let mut col_vals = HashMap::new();
        for t in &vi.linearization.constant_term {
            if let PolishToken::Cell(v) = t {
                let pe = combined.evaluate(v.col).unwrap();
                col_vals.insert((v.col, false), pe.zeta);
                col_vals.insert((v.col, true), pe.zeta_omega);
            }
        }
        let srs_log2 = u64::BITS - 1 - (vi.max_poly_size as u64).leading_zeros();

        let circ = FtCircuit {
            tokens: vi.linearization.constant_term.clone(),
            domain: vi.domain,
            srs_log2,
            endo: vi.endo,
            shifts: vi.shift.to_vec(),
            alpha: oracles.alpha,
            beta: oracles.beta,
            gamma: oracles.gamma,
            zeta: oracles.zeta,
            w: combined.w.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
            s: combined.s.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
            zperm: (combined.z.zeta, combined.z.zeta_omega),
            public_evals0: o.public_evals[0].clone(),
            col_vals,
        };
        // out-of-circuit perm_scalar reference (the only scalar
        // `Plonk_checks.checked` verifies)
        let perm_ref = {
            use crate::plonk_checks::{perm_scalar, scalars_env, Domain, Evals};
            let domain = Domain::<Fp> {
                log2_size: vi.domain.log_size_of_group,
                generator: vi.domain.group_gen,
            };
            let minimal = crate::composition_types::plonk::Minimal::<Fp, Fp, bool> {
                alpha: oracles.alpha,
                beta: oracles.beta,
                gamma: oracles.gamma,
                zeta: oracles.zeta,
                joint_combiner: None,
                feature_flags: crate::composition_types::Features::none(),
            };
            let env = scalars_env::<Fp, bool>(&domain, srs_log2, &minimal);
            let e = Evals {
                w: combined.w.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
                s: combined.s.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
                z: (combined.z.zeta, combined.z.zeta_omega),
            };
            perm_scalar(&env, &e)
        };

        let (mut fpi, fverifier) = circ.compile_to_indexes().unwrap();
        let (fproof, out) = fpi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        assert_eq!(out.0, o.ft_eval0, "in-circuit ft_eval0 matches kimchi");
        assert_eq!(out.1, perm_ref, "in-circuit perm_scalar matches reference");
        fverifier.verify::<BaseSponge, ScalarSponge>(fproof, (), (out.0, out.1));
    }

    struct ActualEvalCircuit {
        chunks: Vec<Fp>,
        pt_to_n: Fp,
    }
    impl SnarkyCircuit for ActualEvalCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        type PublicOutput = FieldVar<Fp>;
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<FieldVar<Fp>> {
            let mut chunks = vec![];
            for &c in &self.chunks {
                chunks.push(sys.compute(loc!(), move |_| c)?);
            }
            let pt: FieldVar<Fp> = sys.compute(loc!(), |_| self.pt_to_n)?;
            actual_evaluation_circuit(sys, loc!(), &chunks, &pt)
        }
    }

    fn actual_evaluation_ref(chunks: &[Fp], pt_to_n: Fp) -> Fp {
        let mut it = chunks.iter().rev();
        let mut acc = *it.next().unwrap();
        for &y in it {
            acc = y + pt_to_n * acc;
        }
        acc
    }

    /// In-circuit chunk combination equals the out-of-circuit Horner reference
    /// (and is the identity on a single chunk).
    #[test]
    fn actual_evaluation_circuit_matches_reference() {
        use ark_ff::UniformRand;
        let mut rng = o1_utils::tests::make_test_rng(None);
        // single chunk is the identity (no constraints, so checked at the
        // reference level only)
        let one = [Fp::rand(&mut rng)];
        assert_eq!(actual_evaluation_ref(&one, Fp::rand(&mut rng)), one[0]);
        for k in [2usize, 3, 5] {
            let chunks: Vec<Fp> = (0..k).map(|_| Fp::rand(&mut rng)).collect();
            let pt_to_n = Fp::rand(&mut rng);
            let expected = actual_evaluation_ref(&chunks, pt_to_n);
            let circ = ActualEvalCircuit { chunks, pt_to_n };
            let (mut pi, ver) = circ.compile_to_indexes().unwrap();
            let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
            assert_eq!(*out, expected);
            ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
        }
    }
}
