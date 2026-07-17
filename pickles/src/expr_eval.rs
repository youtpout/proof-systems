//! In-circuit evaluation of kimchi's linearization `constant_term`.
//!
//! kimchi stores the linearization polynomials in RPN as
//! `Vec<PolishToken<..>>` and evaluates them with [`PolishToken::evaluate`],
//! which requires `F: Field`. A [snarky] `FieldVar` is not a field element
//! (multiplication needs the constraint system), so we walk the same tokens
//! with a stack machine that threads the `RunState`.
//!
//! This unblocks the in-circuit `ft_eval0` of the pickles verifiers without
//! porting the OCaml's generated `scalars.ml`: the exact same token stream
//! kimchi's verifier uses is evaluated over circuit variables.

use std::borrow::Cow;

use ark_ff::{FftField, PrimeField};
use ark_poly::Radix2EvaluationDomain as D;
use kimchi::circuits::{
    berkeley_columns::{BerkeleyChallengeTerm, Column},
    expr::{ConstantTerm, PolishToken, RowOffset},
    gate::CurrOrNext,
};

use snarky::{FieldVar, RunState, SnarkyResult};

/// The finalize domain as seen by the polish evaluator: either a fixed
/// known domain (constants) or the one-hot-selected pseudo domain, whose
/// `ω^{-k}` chain and `ζ^n - 1` were built by `scalars_env_circuit`.
pub enum PolishDomain<'a, F: PrimeField> {
    Fixed(D<F>),
    Selected {
        omegas: &'a crate::ft_eval_circuit::DomainOmegas<F>,
        zeta_to_n_minus_1: &'a FieldVar<F>,
    },
}

/// The environment an in-circuit polish evaluation needs: the challenges and
/// column evaluations as circuit variables, plus the constants of the proof's
/// curve. Column/challenge lookups return already-witnessed variables.
pub struct PolishEnv<'a, F: PrimeField> {
    /// The evaluation domain of the proof being verified. `Selected` carries
    /// the pseudo-domain variables precomputed by
    /// [`crate::ft_eval_circuit::scalars_env_circuit`].
    pub domain: PolishDomain<'a, F>,
    /// `c.endo_coefficient`.
    pub endo_coefficient: F,
    /// The Poseidon MDS matrix.
    pub mds: &'a [Vec<F>],
    /// Number of zero-knowledge rows.
    pub zk_rows: u64,
    /// The evaluation point (zeta), as a circuit variable.
    pub pt: FieldVar<F>,
    /// The precomputed `zk_polynomial` of the scalars env. OCaml's
    /// `vanishes_on_zero_knowledge_and_previous_rows` is this value, computed
    /// ONCE in `scalars_env` — the token must reuse it, not recompute.
    pub zk_polynomial: Option<&'a FieldVar<F>>,
    /// The precomputed `ζ^n - 1` of the scalars env. OCaml's
    /// `unnormalized_lagrange_basis` divides this shared value by
    /// `(ζ - ω^i)` — no per-occurrence power chain.
    pub zeta_to_n_minus_1: Option<&'a FieldVar<F>>,
    /// Challenge lookup (alpha/beta/gamma/joint_combiner).
    pub challenge: &'a dyn Fn(BerkeleyChallengeTerm) -> FieldVar<F>,
    /// Column evaluation lookup at the given row.
    pub column: &'a dyn Fn(Column, CurrOrNext) -> FieldVar<F>,
}

/// `∏_{j=0}^{i-1} (pt - ω^{n-i+j})` in circuit (permutation
/// `eval_vanishes_on_last_n_rows`).
fn vanishes_on_last_n_rows<F: FftField + PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    domain: &D<F>,
    i: u64,
    pt: &FieldVar<F>,
) -> SnarkyResult<FieldVar<F>> {
    if i == 0 {
        return Ok(FieldVar::constant(F::one()));
    }
    let mut term = domain.group_gen.pow([domain.size - i]);
    let mut acc = pt - &FieldVar::constant(term);
    for _ in 0..i - 1 {
        term *= domain.group_gen;
        let factor = pt - &FieldVar::constant(term);
        acc = acc.mul(&factor, None, loc.clone(), sys)?;
    }
    Ok(acc)
}

/// `(pt^n - 1) / (pt - ω^offset)` in circuit
/// (`unnormalized_lagrange_basis`).
fn unnormalized_lagrange_basis<F: FftField + PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    domain: &D<F>,
    offset: i32,
    pt: &FieldVar<F>,
) -> SnarkyResult<FieldVar<F>> {
    let omega_i = if offset < 0 {
        domain.group_gen.pow([(-offset) as u64]).inverse().unwrap()
    } else {
        domain.group_gen.pow([offset as u64])
    };
    // numerator = pt^n - 1
    let pt_n = pow_circuit(sys, loc.clone(), pt, domain.size)?;
    let numerator = &pt_n - &FieldVar::constant(F::one());
    let denominator = pt - &FieldVar::constant(omega_i);
    crate::plonk_curve_ops::div_var(sys, loc, &numerator, &denominator)
}

/// `x²` via a Square constraint (OCaml `Field.square` — NOT a mul's R1CS;
/// the gadget signs differ: square `[0,0,-1,1,0]` vs mul `[0,0,1,-1,0]`).
pub fn square_circuit<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    x: &FieldVar<F>,
) -> SnarkyResult<FieldVar<F>> {
    if let FieldVar::Constant(c) = x {
        return Ok(FieldVar::constant(*c * c));
    }
    let x_clone = x.clone();
    let z: FieldVar<F> = sys.compute(loc.clone(), move |env| {
        let v: F = env.read_var(&x_clone);
        v * v
    })?;
    sys.add_constraint(
        snarky::runner::Constraint::BasicSnarkyConstraint(
            snarky::constraint_system::BasicSnarkyConstraint::Square(x.clone(), z.clone()),
        ),
        Some("square".into()),
        loc,
    )?;
    Ok(z)
}

/// `base^exp` in circuit — OCaml `Plonk_checks.pow`'s exact recursion
/// (plonk_checks.ml:226) with the env's `square x = x * x` (a MUL gadget,
/// plonk_checks.ml:225): `pow x n = x * pow (x*x) (n/2)` when odd,
/// `pow (x*x) (n/2)` when even.
pub fn pow_circuit<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    base: &FieldVar<F>,
    exp: u64,
) -> SnarkyResult<FieldVar<F>> {
    match exp {
        0 => Ok(FieldVar::constant(F::one())),
        1 => Ok(base.clone()),
        _ => {
            let sq = base.mul(&base.clone(), None, loc.clone(), sys)?;
            let y = pow_circuit(sys, loc.clone(), &sq, exp / 2)?;
            if exp & 1 == 1 {
                base.mul(&y, None, loc, sys)
            } else {
                Ok(y)
            }
        }
    }
}

/// Evaluates a polish token stream over circuit variables, mirroring
/// [`PolishToken::evaluate`].
pub fn eval_polish<F: FftField + PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    toks: &[PolishToken<F, Column, BerkeleyChallengeTerm>],
    env: &PolishEnv<F>,
) -> SnarkyResult<FieldVar<F>> {
    let mut stack: Vec<FieldVar<F>> = vec![];
    let mut cache: Vec<FieldVar<F>> = vec![];
    let mut skip_count = 0usize;

    for t in toks {
        if skip_count > 0 {
            skip_count -= 1;
            continue;
        }
        use PolishToken::*;
        match t {
            Challenge(term) => stack.push((env.challenge)(*term)),
            Constant(ConstantTerm::EndoCoefficient) => {
                stack.push(FieldVar::constant(env.endo_coefficient))
            }
            Constant(ConstantTerm::Mds { row, col }) => {
                stack.push(FieldVar::constant(env.mds[*row][*col]))
            }
            Constant(ConstantTerm::Literal(x)) => stack.push(FieldVar::constant(*x)),
            VanishesOnZeroKnowledgeAndPreviousRows if env.zk_polynomial.is_some() => {
                stack.push(env.zk_polynomial.unwrap().clone())
            }
            VanishesOnZeroKnowledgeAndPreviousRows => match &env.domain {
                PolishDomain::Fixed(d) => stack.push(vanishes_on_last_n_rows(
                    sys,
                    loc.clone(),
                    d,
                    env.zk_rows + 1,
                    &env.pt,
                )?),
                PolishDomain::Selected { omegas, .. } => {
                    // (pt - ω^{-(zk+1)})(pt - ω^{-zk})..(pt - ω^{-1}), from
                    // the precomputed ω^{-k} variables (zk_rows = 3).
                    assert_eq!(env.zk_rows, 3, "selected domain assumes zk_rows = 3");
                    let omega_to_zk_minus_1 =
                        omegas
                            .omega_to_zk
                            .mul(&omegas.omega_to_minus_1, None, loc.clone(), sys)?;
                    let mut acc = &env.pt - &omega_to_zk_minus_1;
                    for w in [
                        &omegas.omega_to_zk,
                        &omegas.omega_to_zk_plus_1,
                        &omegas.omega_to_minus_1,
                    ] {
                        let factor = &env.pt - w;
                        acc = acc.mul(&factor, None, loc.clone(), sys)?;
                    }
                    stack.push(acc)
                }
            },
            UnnormalizedLagrangeBasis(RowOffset { zk_rows, offset }) => {
                let off = if *zk_rows {
                    -(env.zk_rows as i32) + offset
                } else {
                    *offset
                };
                match &env.domain {
                    PolishDomain::Fixed(d) if env.zeta_to_n_minus_1.is_some() => {
                        // OCaml env: `(ζ^n - 1) / (ζ - ω^off)` with the SHARED
                        // precomputed numerator (plonk_checks.ml:300).
                        let omega_i = if off < 0 {
                            d.group_gen.pow([(-off) as u64]).inverse().unwrap()
                        } else {
                            d.group_gen.pow([off as u64])
                        };
                        let denominator = &env.pt - &FieldVar::constant(omega_i);
                        stack.push(crate::plonk_curve_ops::div_var(
                            sys,
                            loc.clone(),
                            env.zeta_to_n_minus_1.unwrap(),
                            &denominator,
                        )?)
                    }
                    PolishDomain::Fixed(d) => stack.push(unnormalized_lagrange_basis(
                        sys,
                        loc.clone(),
                        d,
                        off,
                        &env.pt,
                    )?),
                    PolishDomain::Selected {
                        omegas,
                        zeta_to_n_minus_1,
                    } => {
                        // OCaml env's `unnormalized_lagrange_basis`:
                        // (ζ^n - 1) / (ζ - ω^off), reusing the precomputed
                        // vanishing value and ω^{-k} chain.
                        let w_to_i = match off {
                            0 => FieldVar::constant(F::one()),
                            1 => omegas.generator.clone(),
                            -1 => omegas.omega_to_minus_1.clone(),
                            -2 => omegas.omega_to_zk_plus_1.clone(),
                            -3 => omegas.omega_to_zk.clone(),
                            -4 => omegas.omega_to_zk.mul(
                                &omegas.omega_to_minus_1,
                                None,
                                loc.clone(),
                                sys,
                            )?,
                            other => {
                                panic!("unnormalized_lagrange_basis({other}) on a pseudo domain")
                            }
                        };
                        let denominator = &env.pt - &w_to_i;
                        stack.push(crate::plonk_curve_ops::div_var(
                            sys,
                            loc.clone(),
                            zeta_to_n_minus_1,
                            &denominator,
                        )?)
                    }
                }
            }
            Cell(v) => stack.push((env.column)(v.col, v.row)),
            Dup => stack.push(stack[stack.len() - 1].clone()),
            Pow(n) => {
                let i = stack.len() - 1;
                stack[i] = pow_circuit(sys, loc.clone(), &stack[i], *n)?;
            }
            Add => {
                let y = stack.pop().unwrap();
                let x = stack.pop().unwrap();
                stack.push(&x + &y);
            }
            Sub => {
                let y = stack.pop().unwrap();
                let x = stack.pop().unwrap();
                stack.push(&x - &y);
            }
            Mul => {
                let y = stack.pop().unwrap();
                let x = stack.pop().unwrap();
                stack.push(x.mul(&y, None, loc.clone(), sys)?);
            }
            Store => cache.push(stack[stack.len() - 1].clone()),
            Load(i) => stack.push(cache[*i].clone()),
            // Feature-gated tokens only appear with optional gates / lookups,
            // which the base pickles step circuit does not use yet.
            SkipIf(..) | SkipIfNot(..) => {
                panic!("eval_polish: feature-flag tokens not supported in-circuit yet")
            }
        }
    }

    assert_eq!(
        stack.len(),
        1,
        "polish evaluation left a non-singleton stack"
    );
    Ok(stack.pop().unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::plonk_checks::ZK_ROWS;
    use ark_ff::{One, Zero};
    use kimchi::{
        circuits::{
            berkeley_columns::BerkeleyChallenges,
            expr::{Constants, PolishToken},
        },
        curve::KimchiCurve,
    };
    use mina_curves::pasta::{Fp, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::{commitment::PolyComm, ipa::OpeningProof, SRS};
    use snarky::{api::SnarkyCircuit, loc, RunState, SnarkyResult};

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
        ) -> SnarkyResult<Self::PublicOutput> {
            let x: FieldVar<Fp> = sys.compute(loc!(), |_| *private.unwrap())?;
            let xx = x.mul(&x, None, loc!(), sys)?;
            xx.assert_equals(sys, loc!(), &z)?;
            let _ = sys.poseidon(loc!(), (x, z));
            Ok(())
        }
    }

    /// A tiny circuit whose single public output is our in-circuit evaluation
    /// of the linearization constant term for a captured (real) proof.
    struct ConstTermCircuit {
        tokens: Vec<PolishToken<Fp, Column, BerkeleyChallengeTerm>>,
        domain: D<Fp>,
        endo: Fp,
        alpha: Fp,
        beta: Fp,
        gamma: Fp,
        // (column, is_next) -> value; captured out of circuit
        col_vals: std::collections::HashMap<(Column, bool), Fp>,
    }

    impl SnarkyCircuit for ConstTermCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = Fp;
        type PublicInput = ();
        type PublicOutput = FieldVar<Fp>;

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let pt: FieldVar<Fp> = sys.compute(loc!(), |_| *private.unwrap())?;
            let mds = &Vesta::sponge_params().mds;
            let mds: Vec<Vec<Fp>> = mds.iter().map(|r| r.to_vec()).collect();
            // witness challenges and column evaluations, so the whole
            // evaluation flows through real circuit variables
            let alpha_v: FieldVar<Fp> = sys.compute(loc!(), |_| self.alpha)?;
            let beta_v: FieldVar<Fp> = sys.compute(loc!(), |_| self.beta)?;
            let gamma_v: FieldVar<Fp> = sys.compute(loc!(), |_| self.gamma)?;
            let mut col_map: std::collections::HashMap<(Column, bool), FieldVar<Fp>> =
                std::collections::HashMap::new();
            for (&(col, is_next), &v) in &self.col_vals {
                let fv: FieldVar<Fp> = sys.compute(loc!(), move |_| v)?;
                col_map.insert((col, is_next), fv);
            }
            let challenge = move |t: BerkeleyChallengeTerm| match t {
                BerkeleyChallengeTerm::Alpha => alpha_v.clone(),
                BerkeleyChallengeTerm::Beta => beta_v.clone(),
                BerkeleyChallengeTerm::Gamma => gamma_v.clone(),
                BerkeleyChallengeTerm::JointCombiner => FieldVar::constant(Fp::zero()),
            };
            let column = move |col: Column, row: CurrOrNext| {
                let is_next = matches!(row, CurrOrNext::Next);
                col_map[&(col, is_next)].clone()
            };
            let env = PolishEnv {
                domain: PolishDomain::Fixed(self.domain),
                endo_coefficient: self.endo,
                mds: &mds,
                zk_rows: ZK_ROWS as u64,
                pt,
                zk_polynomial: None,
                zeta_to_n_minus_1: None,
                challenge: &challenge,
                column: &column,
            };
            eval_polish(sys, loc!(), &self.tokens, &env)
        }
    }

    /// Our in-circuit constant-term evaluator matches kimchi's out-of-circuit
    /// PolishToken evaluation on a real proof's linearization.
    #[test]
    fn constant_term_circuit_matches_kimchi() {
        // 1) get a real proof + its oracles
        let mut prover_index = SmallCircuit {}.compile_to_indexes().unwrap().0;
        let vi = {
            let (_, vi) = SmallCircuit {}.compile_to_indexes().unwrap();
            vi
        };
        let vi = &vi.index;
        let x = Fp::from(5u64);
        let z = x * x;
        let (proof, _) = prover_index
            .prove::<BaseSponge, ScalarSponge>(z, x, true)
            .unwrap();
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

        // 2) kimchi's out-of-circuit value
        let constants = Constants {
            endo_coefficient: vi.endo,
            mds: &Vesta::sponge_params().mds,
            zk_rows: ZK_ROWS as u64,
        };
        let challenges = BerkeleyChallenges {
            alpha: oracles.alpha,
            beta: oracles.beta,
            gamma: oracles.gamma,
            joint_combiner: Fp::zero(),
        };
        let expected = PolishToken::evaluate(
            &vi.linearization.constant_term,
            vi.domain,
            oracles.zeta,
            &combined,
            &constants,
            &challenges,
        )
        .unwrap();

        // 3) capture the column values referenced by the tokens
        let mut col_vals = std::collections::HashMap::new();
        for t in &vi.linearization.constant_term {
            if let PolishToken::Cell(v) = t {
                use kimchi::circuits::expr::ColumnEvaluations;
                let pe = combined.evaluate(v.col).unwrap();
                col_vals.insert((v.col, false), pe.zeta);
                col_vals.insert((v.col, true), pe.zeta_omega);
            }
        }

        // 4) evaluate in circuit and prove
        let circ = ConstTermCircuit {
            tokens: vi.linearization.constant_term.clone(),
            domain: vi.domain,
            endo: vi.endo,
            alpha: oracles.alpha,
            beta: oracles.beta,
            gamma: oracles.gamma,
            col_vals,
        };
        let (mut pi, verifier) = circ.compile_to_indexes().unwrap();
        let (proof2, out) = pi
            .prove::<BaseSponge, ScalarSponge>((), oracles.zeta, true)
            .unwrap();
        assert_eq!(*out, expected, "in-circuit constant term matches kimchi");
        verifier.verify::<BaseSponge, ScalarSponge>(proof2, (), *out);
    }

    /// The generated-scalars.ml tree evaluates to the same value as kimchi's
    /// PolishToken stream (pure-value comparison, Tick side).
    #[test]
    fn scalars_ml_value_matches_kimchi() {
        let mut prover_index = SmallCircuit {}.compile_to_indexes().unwrap().0;
        let vi = {
            let (_, vi) = SmallCircuit {}.compile_to_indexes().unwrap();
            vi
        };
        let vi = &vi.index;
        let x = Fp::from(5u64);
        let z = x * x;
        let (proof, _) = prover_index
            .prove::<BaseSponge, ScalarSponge>(z, x, true)
            .unwrap();
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

        let constants = Constants {
            endo_coefficient: vi.endo,
            mds: &Vesta::sponge_params().mds,
            zk_rows: ZK_ROWS as u64,
        };
        let challenges = BerkeleyChallenges {
            alpha: oracles.alpha,
            beta: oracles.beta,
            gamma: oracles.gamma,
            joint_combiner: Fp::zero(),
        };
        let expected = PolishToken::evaluate(
            &vi.linearization.constant_term,
            vi.domain,
            oracles.zeta,
            &combined,
            &constants,
            &challenges,
        )
        .unwrap();

        let column = |col: Column, row: CurrOrNext| -> Fp {
            use kimchi::circuits::expr::ColumnEvaluations;
            let pe = combined.evaluate(col).unwrap();
            match row {
                CurrOrNext::Curr => pe.zeta,
                CurrOrNext::Next => pe.zeta_omega,
            }
        };
        let mds_vecs: Vec<Vec<Fp>> = Vesta::sponge_params()
            .mds
            .iter()
            .map(|row| row.to_vec())
            .collect();
        let actual = crate::scalars_ml::eval_constant_term_value(
            crate::scalars_ml::ScalarsKind::Tick,
            &column,
            oracles.alpha,
            oracles.beta,
            oracles.gamma,
            vi.endo,
            &mds_vecs,
            vi.domain,
            oracles.zeta,
            ZK_ROWS as u64,
        );
        let mut th = std::collections::HashMap::new();
        for t in &vi.linearization.constant_term {
            *th.entry(format!("{t:?}").split(['(', ' ']).next().unwrap().to_string())
                .or_insert(0usize) += 1;
        }
        let mut tv: Vec<_> = th.into_iter().collect();
        tv.sort();
        {
            use std::hash::{Hash, Hasher};
            let mut h = std::collections::hash_map::DefaultHasher::new();
            format!("{:?}", vi.linearization.constant_term).hash(&mut h);
            eprintln!("[small-circuit] tokens={} streamhash={:x} hist={tv:?}", vi.linearization.constant_term.len(), h.finish());
        }
        assert_eq!(actual, expected, "scalars.ml tree value matches kimchi");
    }

    /// Offline reproduction of a recorded finalize divergence: loads the
    /// inputs dumped by the SCALARS_DEBUG block and compares kimchi's
    /// PolishToken evaluation against the scalars.ml tree, dumping the
    /// intermediate Store/cache values for bisection.
    #[test]
    fn scalars_ml_offline_repro() {
        let path = "/tmp/claude-1000/scalars_fail.json";
        let Ok(data) = std::fs::read_to_string(path) else {
            eprintln!("no {path}, skipping");
            return;
        };
        let obj: std::collections::HashMap<String, String> = serde_json::from_str(&data).unwrap();
        let f = |k: &str| -> Fp {
            use std::str::FromStr;
            Fp::from_str(&obj[k]).unwrap()
        };
        let mut cellmap: std::collections::HashMap<(Column, bool), Fp> =
            std::collections::HashMap::new();
        for (k, v) in &obj {
            if let Some(rest) = k.strip_prefix("cell ") {
                use std::str::FromStr;
                let (colstr, next) = rest.rsplit_once(' ').unwrap();
                let next = next == "true";
                let col = if let Some(i) = colstr
                    .strip_prefix("Witness(")
                    .and_then(|s| s.strip_suffix(")"))
                {
                    Column::Witness(i.parse().unwrap())
                } else if let Some(i) = colstr
                    .strip_prefix("Coefficient(")
                    .and_then(|s| s.strip_suffix(")"))
                {
                    Column::Coefficient(i.parse().unwrap())
                } else if let Some(g) = colstr
                    .strip_prefix("Index(")
                    .and_then(|s| s.strip_suffix(")"))
                {
                    use kimchi::circuits::gate::GateType::*;
                    Column::Index(match g {
                        "Generic" => Generic,
                        "Poseidon" => Poseidon,
                        "CompleteAdd" => CompleteAdd,
                        "VarBaseMul" => VarBaseMul,
                        "EndoMul" => EndoMul,
                        "EndoMulScalar" => EndoMulScalar,
                        _ => panic!("{g}"),
                    })
                } else {
                    panic!("{colstr}")
                };
                cellmap.insert((col, next), Fp::from_str(v).unwrap());
            }
        }
        let (alpha, beta, gamma, zeta) = (f("alpha"), f("beta"), f("gamma"), f("zeta"));

        // tokens from a compiled small circuit (stream-hash-identical)
        let vi = {
            let (_, vi) = SmallCircuit {}.compile_to_indexes().unwrap();
            vi
        };
        let vi = &vi.index;

        struct MapEvals(std::collections::HashMap<(Column, bool), Fp>);
        impl kimchi::circuits::expr::ColumnEvaluations<Fp> for MapEvals {
            type Column = Column;
            fn evaluate(
                &self,
                col: Column,
            ) -> Result<
                kimchi::proof::PointEvaluations<Fp>,
                kimchi::circuits::expr::ExprError<Column>,
            > {
                Ok(kimchi::proof::PointEvaluations {
                    zeta: *self.0.get(&(col, false)).unwrap_or(&Fp::from(0u64)),
                    zeta_omega: *self.0.get(&(col, true)).unwrap_or(&Fp::from(0u64)),
                })
            }
        }
        let constants = Constants {
            endo_coefficient: vi.endo,
            mds: &Vesta::sponge_params().mds,
            zk_rows: ZK_ROWS as u64,
        };
        let challenges = BerkeleyChallenges {
            alpha,
            beta,
            gamma,
            joint_combiner: Fp::zero(),
        };
        let polish_val = PolishToken::evaluate(
            &vi.linearization.constant_term,
            vi.domain,
            zeta,
            &MapEvals(cellmap.clone()),
            &constants,
            &challenges,
        )
        .unwrap();
        let column = |col: Column, row: CurrOrNext| -> Fp {
            *cellmap
                .get(&(col, matches!(row, CurrOrNext::Next)))
                .unwrap_or(&Fp::from(0u64))
        };
        let mds_vecs: Vec<Vec<Fp>> = Vesta::sponge_params()
            .mds
            .iter()
            .map(|row| row.to_vec())
            .collect();
        let tree_val = crate::scalars_ml::eval_constant_term_value(
            crate::scalars_ml::ScalarsKind::Tick,
            &column,
            alpha,
            beta,
            gamma,
            vi.endo,
            &mds_vecs,
            vi.domain,
            zeta,
            ZK_ROWS as u64,
        );
        eprintln!("recorded polish={} ml={}", obj["polish"], obj["ml"]);
        eprintln!("offline  polish={polish_val:?} tree={tree_val:?}");

        // bisect per gate: keep only one Index selector non-zero at a time
        use kimchi::circuits::gate::GateType::*;
        for g in [
            Generic,
            Poseidon,
            CompleteAdd,
            VarBaseMul,
            EndoMul,
            EndoMulScalar,
        ] {
            let mut m = cellmap.clone();
            for gg in [
                Generic,
                Poseidon,
                CompleteAdd,
                VarBaseMul,
                EndoMul,
                EndoMulScalar,
            ] {
                if gg != g {
                    m.insert((Column::Index(gg), false), Fp::from(0u64));
                    m.insert((Column::Index(gg), true), Fp::from(0u64));
                }
            }
            let pv = PolishToken::evaluate(
                &vi.linearization.constant_term,
                vi.domain,
                zeta,
                &MapEvals(m.clone()),
                &constants,
                &challenges,
            )
            .unwrap();
            let colf = |col: Column, row: CurrOrNext| -> Fp {
                *m.get(&(col, matches!(row, CurrOrNext::Next)))
                    .unwrap_or(&Fp::from(0u64))
            };
            let tv = crate::scalars_ml::eval_constant_term_value(
                crate::scalars_ml::ScalarsKind::Tick,
                &colf,
                alpha,
                beta,
                gamma,
                vi.endo,
                &mds_vecs,
                vi.domain,
                zeta,
                ZK_ROWS as u64,
            );
            eprintln!(
                "gate {g:?}: {}",
                if pv == tv { "MATCH" } else { "DIVERGES" }
            );
        }

        // perturbation probe: which cells influence the delta?
        let eval_both = |m: &std::collections::HashMap<(Column, bool), Fp>| -> (Fp, Fp) {
            let pv = PolishToken::evaluate(
                &vi.linearization.constant_term,
                vi.domain,
                zeta,
                &MapEvals(m.clone()),
                &constants,
                &challenges,
            )
            .unwrap();
            let colf = |col: Column, row: CurrOrNext| -> Fp {
                *m.get(&(col, matches!(row, CurrOrNext::Next)))
                    .unwrap_or(&Fp::from(0u64))
            };
            let tv = crate::scalars_ml::eval_constant_term_value(
                crate::scalars_ml::ScalarsKind::Tick,
                &colf,
                alpha,
                beta,
                gamma,
                vi.endo,
                &mds_vecs,
                vi.domain,
                zeta,
                ZK_ROWS as u64,
            );
            (pv, tv)
        };
        let (p0, t0) = eval_both(&cellmap);
        let d0 = p0 - t0;
        let mut keys: Vec<_> = cellmap.keys().cloned().collect();
        keys.sort_by_key(|k| format!("{k:?}"));
        for k in keys {
            let mut m = cellmap.clone();
            *m.get_mut(&k).unwrap() += Fp::from(1u64);
            let (p, t) = eval_both(&m);
            if p - t != d0 {
                eprintln!("delta sensitive to {k:?}");
            }
        }
        assert_eq!(polish_val, tree_val, "offline polish vs tree");
    }
}
