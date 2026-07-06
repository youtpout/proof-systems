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

use snarky::{FieldVar, RunState, SnarkyResult};

use crate::expr_eval::pow_circuit;

/// The scalars environment as circuit variables (mirror of
/// [crate::plonk_checks::ScalarsEnv]).
pub struct ScalarsEnvVar<F: PrimeField> {
    pub alpha_pows: Vec<FieldVar<F>>,
    pub zk_polynomial: FieldVar<F>,
    pub omega_to_minus_zk_rows: F,
    pub zeta_to_n_minus_1: FieldVar<F>,
    pub zeta_to_srs_length: FieldVar<F>,
    pub beta: FieldVar<F>,
    pub gamma: FieldVar<F>,
    pub zeta: FieldVar<F>,
}

impl<F: PrimeField> ScalarsEnvVar<F> {
    pub fn alpha_pow(&self, i: usize) -> FieldVar<F> {
        self.alpha_pows[i].clone()
    }
}

/// Builds the in-circuit scalars environment from the challenge variables
/// `alpha`, `beta`, `gamma`, `zeta` (`zk_rows = 3`).
#[allow(clippy::too_many_arguments)]
pub fn scalars_env_circuit<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    domain: &D<F>,
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

    let omega_to_minus_1 = domain.group_gen.inverse().unwrap();
    let omega_to_zk_plus_1 = omega_to_minus_1.square();
    let omega_to_zk = omega_to_zk_plus_1 * omega_to_minus_1;

    // zk_polynomial = (zeta - w^-1)(zeta - w^-2)(zeta - w^-3)
    let f1 = zeta - &FieldVar::constant(omega_to_minus_1);
    let f2 = zeta - &FieldVar::constant(omega_to_zk_plus_1);
    let f3 = zeta - &FieldVar::constant(omega_to_zk);
    let f12 = f1.mul(&f2, None, loc.clone(), sys)?;
    let zk_polynomial = f12.mul(&f3, None, loc.clone(), sys)?;

    let zeta_n = pow_circuit(sys, loc.clone(), zeta, domain.size)?;
    let zeta_to_n_minus_1 = &zeta_n - &FieldVar::constant(F::one());
    let zeta_to_srs_length = pow_circuit(sys, loc, zeta, 1u64 << srs_length_log2)?;

    Ok(ScalarsEnvVar {
        alpha_pows,
        zk_polynomial,
        omega_to_minus_zk_rows: omega_to_zk,
        zeta_to_n_minus_1,
        zeta_to_srs_length,
        beta,
        gamma,
        zeta: zeta.clone(),
    })
}

/// The proof evaluations as circuit variables.
pub struct EvalsVar<F: PrimeField> {
    pub w: Vec<(FieldVar<F>, FieldVar<F>)>,
    pub s: Vec<(FieldVar<F>, FieldVar<F>)>,
    pub z: (FieldVar<F>, FieldVar<F>),
}

/// In-circuit `ft_eval0` (mirror of [crate::plonk_checks::ft_eval0]).
/// `constant_term` comes from [crate::expr_eval::eval_polish].
pub fn ft_eval0_circuit<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    env: &ScalarsEnvVar<F>,
    shifts: &[F],
    e: &EvalsVar<F>,
    p_eval0: &[FieldVar<F>],
    constant_term: &FieldVar<F>,
) -> SnarkyResult<FieldVar<F>> {
    use crate::plonk_checks::PERM_ALPHA0;

    let zkp = &env.zk_polynomial;
    let zeta1m1 = &env.zeta_to_n_minus_1;
    let (beta, gamma, zeta) = (&env.beta, &env.gamma, &env.zeta);

    // combine public-eval chunks by powers of zeta^{srs_length}
    let mut chunks = p_eval0.iter().rev();
    let mut p = chunks.next().expect("empty public evals").clone();
    for chunk in chunks {
        let scaled = env.zeta_to_srs_length.mul(&p, None, loc.clone(), sys)?;
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
            let bs = beta.mul(s, None, loc.clone(), sys)?;
            let factor = &(&bs + &w0[i]) + gamma;
            acc = acc.mul(&factor, None, loc.clone(), sys)?;
        }
        acc
    };

    ft = &ft - &p_eval0;

    // subtract the shift product term:
    // alpha^0 * zkp * z(zeta) * prod_i (gamma + beta*zeta*s_i + w0_i)
    ft = {
        let a0zkp = env
            .alpha_pow(PERM_ALPHA0)
            .mul(zkp, None, loc.clone(), sys)?;
        let mut acc = a0zkp.mul(&e.z.0, None, loc.clone(), sys)?;
        let beta_zeta = beta.mul(zeta, None, loc.clone(), sys)?;
        for (i, s) in shifts.iter().enumerate() {
            let bzs = beta_zeta.scale(*s);
            let factor = &(gamma + &bzs) + &w0[i];
            acc = acc.mul(&factor, None, loc.clone(), sys)?;
        }
        &ft - &acc
    };

    // + numerator / denominator
    let one = FieldVar::constant(F::one());
    let om_zk = FieldVar::constant(env.omega_to_minus_zk_rows);
    let zeta_minus_omzk = zeta - &om_zk;
    let zeta_minus_1 = zeta - &one;
    let a1 = env.alpha_pow(PERM_ALPHA0 + 1);
    let a2 = env.alpha_pow(PERM_ALPHA0 + 2);
    let term1 =
        zeta1m1
            .mul(&a1, None, loc.clone(), sys)?
            .mul(&zeta_minus_omzk, None, loc.clone(), sys)?;
    let term2 =
        zeta1m1
            .mul(&a2, None, loc.clone(), sys)?
            .mul(&zeta_minus_1, None, loc.clone(), sys)?;
    let one_minus_z0 = &one - &e.z.0;
    let numerator = (&term1 + &term2).mul(&one_minus_z0, None, loc.clone(), sys)?;
    let denominator = zeta_minus_omzk.mul(&zeta_minus_1, None, loc.clone(), sys)?;
    let frac = crate::plonk_curve_ops::div_var(sys, loc, &numerator, &denominator)?;
    ft = &ft + &frac;

    Ok(&ft - constant_term)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr_eval::{eval_polish, PolishEnv};
    use crate::plonk_checks::ZK_ROWS;
    use ark_ff::{One, Zero};
    use kimchi::circuits::berkeley_columns::{BerkeleyChallengeTerm, Column};
    use kimchi::circuits::expr::{ColumnEvaluations, PolishToken};
    use kimchi::circuits::gate::CurrOrNext;
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::commitment::PolyComm;
    use poly_commitment::ipa::OpeningProof;
    use poly_commitment::SRS;
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
        type PublicOutput = FieldVar<Fp>;

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            _private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<FieldVar<Fp>> {
            let w = |sys: &mut RunState<Fp>, v: Fp| sys.compute(loc!(), move |_| v);
            let zeta = w(sys, self.zeta)?;
            let alpha = w(sys, self.alpha)?;
            let beta = w(sys, self.beta)?;
            let gamma = w(sys, self.gamma)?;

            // scalars env in-circuit
            let env = scalars_env_circuit(
                sys,
                loc!(),
                &self.domain,
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
                domain: self.domain,
                endo_coefficient: self.endo,
                mds: &mds,
                zk_rows: ZK_ROWS as u64,
                pt: zeta.clone(),
                challenge: &challenge,
                column: &column,
            };
            let constant_term = eval_polish(sys, loc!(), &self.tokens, &penv)?;

            ft_eval0_circuit(
                sys,
                loc!(),
                &env,
                &self.shifts,
                &evals,
                &p_eval0,
                &constant_term,
            )
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
        let (mut fpi, fverifier) = circ.compile_to_indexes().unwrap();
        let (fproof, out) = fpi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        assert_eq!(*out, o.ft_eval0, "in-circuit ft_eval0 matches kimchi");
        fverifier.verify::<BaseSponge, ScalarSponge>(fproof, (), *out);
    }
}
