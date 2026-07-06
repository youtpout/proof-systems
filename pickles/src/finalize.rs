//! The arithmetic core of `finalize_other_proof` (pickles `wrap_verifier.ml`),
//! assembled in-circuit from the previously-ported and separately-validated
//! primitives:
//!
//! - [`crate::fr_sponge::squeeze_xi_r`] — resamples the 128-bit challenges
//!   `xi` (polyscale) and `r` (evalscale) from the Fiat-Shamir transcript;
//! - [`crate::scalar_challenge::scalar_to_field`] — the endo interpretation of
//!   those challenges as full field elements;
//! - [`crate::ft_eval_circuit`] — the in-circuit `ft_eval0`;
//! - [`crate::ipa::combined_inner_product_circuit`] — the deferred inner
//!   product `Σ_i xi^i (zeta_i + r·zetaw_i)`.
//!
//! This covers steps 4–8 of the OCaml `finalize_other_proof`: reconstruct the
//! sponge, squeeze and check `xi`, and check the combined inner product. The
//! remaining two conjuncts of the returned `Boolean.all` — `b_correct` (the new
//! bulletproof-challenge polynomial) and `plonk_checks_passed` (the full
//! per-gate PlonK relation) — are left for later.
//!
//! The `xi_correct` check compares the *raw 128-bit* squeezed challenge against
//! the claimed `xi` (as OCaml does on `Scalar_challenge.inner`); the field form
//! used by the inner product then comes from `scalar_to_field` of the claimed
//! `xi` (equal to the squeezed one whenever the check passes).

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{FieldVar, RunState, SnarkyResult};

use crate::fr_sponge::{FrSpongeInputs, squeeze_xi_r};
use crate::ipa::{challenge_polynomial_circuit, combined_inner_product_circuit};
use crate::scalar_challenge::scalar_to_field;

/// The result of the finalize arithmetic core: the derived field challenges and
/// the reconstructed inner product, plus the `xi_correct` boolean.
pub struct FinalizeCore<F: PrimeField> {
    /// `xi` (polyscale) as a full field element.
    pub xi_field: FieldVar<F>,
    /// `r` (evalscale) as a full field element.
    pub r_field: FieldVar<F>,
    /// The reconstructed combined inner product.
    pub combined_inner_product: FieldVar<F>,
    /// Whether the squeezed `xi` matched the claimed one (raw 128-bit compare).
    pub xi_correct: FieldVar<F>,
}

/// Runs the finalize arithmetic core.
///
/// - `sponge_inputs` feeds the Fr-sponge (see [`FrSpongeInputs`]);
/// - `claimed_xi` is the deferred/claimed 128-bit `xi` from the statement;
/// - `ft_eval0` is the in-circuit `ft_eval0` (from [`crate::ft_eval_circuit`]);
/// - `cip_entries` are the inner-product columns in kimchi's order, as
///   `(eval_at_zeta, eval_at_zetaw)` field pairs (public, `[ft0, ft1]`, then the
///   mandatory columns);
/// - `endo` is the scalar endomorphism coefficient of the proof's curve.
pub fn finalize_core<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    sponge_inputs: &FrSpongeInputs<F>,
    claimed_xi: &FieldVar<F>,
    cip_entries: &[(FieldVar<F>, FieldVar<F>)],
    endo: F,
) -> SnarkyResult<FinalizeCore<F>> {
    // steps 4-5: reconstruct the sponge, squeeze xi and r (128-bit challenges)
    let (xi_actual, r_actual) = squeeze_xi_r(sys, loc.clone(), sponge_inputs)?;

    // xi_correct: the squeezed xi matches the claimed one (raw 128-bit compare)
    let xi_correct = xi_actual
        .equal(sys, loc.clone(), claimed_xi)?
        .to_field_var();

    // convert the (claimed) xi and r to field elements via the endomorphism
    let xi_field = scalar_to_field(sys, loc.clone(), claimed_xi, endo)?;
    let r_field = scalar_to_field(sys, loc.clone(), &r_actual, endo)?;

    // step 8: the combined inner product from those challenges
    let combined_inner_product =
        combined_inner_product_circuit(sys, loc, &xi_field, &r_field, cip_entries)?;

    Ok(FinalizeCore {
        xi_field,
        r_field,
        combined_inner_product,
        xi_correct,
    })
}

/// The bulletproof `b` value, reconstructed from the *new* bulletproof
/// challenges (step 9 of `finalize_other_proof`):
/// `b = h(zeta) + r * h(zetaw)` where `h(X) = prod_i (1 + chals[i] X^{2^{k-1-i}})`
/// is the challenge polynomial and `zetaw = domain_generator * zeta`.
///
/// `chals` are the challenges already in field form (via
/// [`crate::ipa::compute_challenges`] / [`scalar_to_field`]).
pub fn b_actual<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    chals: &[FieldVar<F>],
    zeta: &FieldVar<F>,
    domain_generator: F,
    r: &FieldVar<F>,
) -> SnarkyResult<FieldVar<F>> {
    let zetaw = zeta.scale(domain_generator);
    let h_zeta = challenge_polynomial_circuit(sys, loc.clone(), chals, zeta)?;
    let h_zetaw = challenge_polynomial_circuit(sys, loc.clone(), chals, &zetaw)?;
    let r_h_zetaw = r.mul(&h_zetaw, None, loc, sys)?;
    Ok(&h_zeta + &r_h_zetaw)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr_eval::{eval_polish, PolishEnv};
    use crate::fr_sponge::{AbsorbEvalsVar, PointEvalVar};
    use crate::ft_eval_circuit::{ft_eval0_circuit, scalars_env_circuit, EvalsVar};
    use crate::plonk_checks::ZK_ROWS;
    use ark_ff::{One, Zero};
    use ark_poly::Radix2EvaluationDomain as D;
    use kimchi::circuits::berkeley_columns::{BerkeleyChallengeTerm, Column};
    use kimchi::circuits::expr::{ColumnEvaluations, PolishToken};
    use kimchi::circuits::gate::CurrOrNext;
    use kimchi::curve::KimchiCurve;
    use kimchi::proof::PointEvaluations;
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

    /// Everything the finalize core needs, captured from a real proof.
    struct FinalizeCircuit {
        // ft_eval0 inputs
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
        // fr-sponge inputs
        digest: Fp,
        ft_eval1: Fp,
        public_evals: [Vec<Fp>; 2],
        e_z: (Vec<Fp>, Vec<Fp>),
        generic: (Vec<Fp>, Vec<Fp>),
        poseidon: (Vec<Fp>, Vec<Fp>),
        complete_add: (Vec<Fp>, Vec<Fp>),
        mul: (Vec<Fp>, Vec<Fp>),
        emul: (Vec<Fp>, Vec<Fp>),
        endomul_scalar: (Vec<Fp>, Vec<Fp>),
        e_w: Vec<(Vec<Fp>, Vec<Fp>)>,
        coefficients: Vec<(Vec<Fp>, Vec<Fp>)>,
        e_s: Vec<(Vec<Fp>, Vec<Fp>)>,
        // cip column order (mandatory columns, single-chunk)
        cip_cols: Vec<(Fp, Fp)>,
        // claimed challenge (raw 128-bit)
        claimed_xi: Fp,
        endo_r: Fp,
    }

    impl SnarkyCircuit for FinalizeCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        // ((xi_field, r_field), (combined_inner_product, xi_correct))
        // (nested because SnarkyType tuples top out at arity 3)
        type PublicOutput = (
            (FieldVar<Fp>, FieldVar<Fp>),
            (FieldVar<Fp>, FieldVar<Fp>),
        );

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            _private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let w1 = |sys: &mut RunState<Fp>, v: Fp| sys.compute(loc!(), move |_| v);
            let wvec = |sys: &mut RunState<Fp>, vs: &[Fp]| -> SnarkyResult<Vec<FieldVar<Fp>>> {
                let mut out = vec![];
                for &v in vs {
                    out.push(sys.compute(loc!(), move |_| v)?);
                }
                Ok(out)
            };
            let wpair =
                |sys: &mut RunState<Fp>, p: (Fp, Fp)| -> SnarkyResult<(FieldVar<Fp>, FieldVar<Fp>)> {
                    Ok((sys.compute(loc!(), move |_| p.0)?, sys.compute(loc!(), move |_| p.1)?))
                };
            let wvpair = |sys: &mut RunState<Fp>,
                          p: &(Vec<Fp>, Vec<Fp>)|
             -> SnarkyResult<PointEvalVar<Fp>> {
                Ok((wvec(sys, &p.0)?, wvec(sys, &p.1)?))
            };

            // ---- in-circuit ft_eval0 ----
            let zeta = w1(sys, self.zeta)?;
            let alpha = w1(sys, self.alpha)?;
            let beta = w1(sys, self.beta)?;
            let gamma = w1(sys, self.gamma)?;
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
            let mut ew = vec![];
            for &p in &self.w {
                ew.push(wpair(sys, p)?);
            }
            let mut es = vec![];
            for &p in &self.s {
                es.push(wpair(sys, p)?);
            }
            let ez = wpair(sys, self.zperm)?;
            let ft_evals = EvalsVar { w: ew, s: es, z: ez };
            let mut p_eval0 = vec![];
            for &v in &self.public_evals0 {
                p_eval0.push(w1(sys, v)?);
            }
            let mds = &Vesta::sponge_params().mds;
            let mds: Vec<Vec<Fp>> = mds.iter().map(|r| r.to_vec()).collect();
            let mut col_map: HashMap<(Column, bool), FieldVar<Fp>> = HashMap::new();
            for (&(col, is_next), &v) in &self.col_vals {
                col_map.insert((col, is_next), w1(sys, v)?);
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
            let ft_eval0 =
                ft_eval0_circuit(sys, loc!(), &env, &self.shifts, &ft_evals, &p_eval0, &constant_term)?;

            // ---- fr-sponge inputs ----
            let digest = w1(sys, self.digest)?;
            let ft_eval1 = w1(sys, self.ft_eval1)?;
            let public_evals = [wvec(sys, &self.public_evals[0])?, wvec(sys, &self.public_evals[1])?];
            let evals = AbsorbEvalsVar {
                z: wvpair(sys, &self.e_z)?,
                generic_selector: wvpair(sys, &self.generic)?,
                poseidon_selector: wvpair(sys, &self.poseidon)?,
                complete_add_selector: wvpair(sys, &self.complete_add)?,
                mul_selector: wvpair(sys, &self.mul)?,
                emul_selector: wvpair(sys, &self.emul)?,
                endomul_scalar_selector: wvpair(sys, &self.endomul_scalar)?,
                w: {
                    let mut v = vec![];
                    for p in &self.e_w {
                        v.push(wvpair(sys, p)?);
                    }
                    v
                },
                coefficients: {
                    let mut v = vec![];
                    for p in &self.coefficients {
                        v.push(wvpair(sys, p)?);
                    }
                    v
                },
                s: {
                    let mut v = vec![];
                    for p in &self.e_s {
                        v.push(wvpair(sys, p)?);
                    }
                    v
                },
            };
            let sponge_inputs = FrSpongeInputs {
                digest,
                prev_challenges: vec![],
                ft_eval1: ft_eval1.clone(),
                public_evals,
                evals,
            };

            // ---- cip entries: public, [ft0, ft1], then mandatory columns ----
            let mut cip_entries = vec![];
            cip_entries.push((
                w1(sys, self.public_evals[0][0])?,
                w1(sys, self.public_evals[1][0])?,
            ));
            cip_entries.push((ft_eval0, ft_eval1));
            for &p in &self.cip_cols {
                cip_entries.push(wpair(sys, p)?);
            }

            let claimed_xi = w1(sys, self.claimed_xi)?;

            let core = finalize_core(
                sys,
                loc!(),
                &sponge_inputs,
                &claimed_xi,
                &cip_entries,
                self.endo_r,
            )?;
            Ok((
                (core.xi_field, core.r_field),
                (core.combined_inner_product, core.xi_correct),
            ))
        }
    }

    /// captured (field-form) bulletproof challenges + points, replayed to check
    /// the in-circuit `b_actual` against the out-of-circuit reference.
    struct BActualCircuit {
        chals: Vec<Fp>,
        zeta: Fp,
        gen: Fp,
        r: Fp,
    }
    impl SnarkyCircuit for BActualCircuit {
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
            let mut chals = vec![];
            for &c in &self.chals {
                chals.push(sys.compute(loc!(), move |_| c)?);
            }
            let zeta: FieldVar<Fp> = sys.compute(loc!(), |_| self.zeta)?;
            let r: FieldVar<Fp> = sys.compute(loc!(), |_| self.r)?;
            b_actual(sys, loc!(), &chals, &zeta, self.gen, &r)
        }
    }

    /// In-circuit `b_actual` = h(zeta) + r*h(zetaw) equals the out-of-circuit
    /// reference on challenges derived from real prechallenges.
    #[test]
    fn b_actual_matches_reference() {
        use crate::common::TOCK_ROUNDS;
        use crate::ipa::{challenge_polynomial, compute_challenges};
        use crate::scalar_challenge::ScalarChallenge;
        use ark_ff::UniformRand;

        let mut rng = o1_utils::tests::make_test_rng(None);
        let (_, endo_r) = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();

        let prechallenges: Vec<_> = (0..TOCK_ROUNDS)
            .map(|_| crate::composition_types::BulletproofChallenge {
                prechallenge: ScalarChallenge(Fp::from(u128::rand(&mut rng))),
            })
            .collect();
        let chals = compute_challenges(&prechallenges, *endo_r);

        let domain_gen = {
            use ark_poly::EvaluationDomain;
            D::<Fp>::new(1 << 5).unwrap().group_gen
        };
        let zeta = Fp::rand(&mut rng);
        let r = Fp::rand(&mut rng);
        let zetaw = domain_gen * zeta;
        let expected = challenge_polynomial(&chals, zeta) + r * challenge_polynomial(&chals, zetaw);

        let circ = BActualCircuit {
            chals,
            zeta,
            gen: domain_gen,
            r,
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        assert_eq!(*out, expected, "in-circuit b_actual matches reference");
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }

    /// The full finalize arithmetic core (sponge -> scalar_to_field -> cip, with
    /// in-circuit ft_eval0) reproduces kimchi's oracles on a real proof.
    #[test]
    fn finalize_core_matches_kimchi() {
        let mut pi = SmallCircuit {}.compile_to_indexes().unwrap().0;
        let vi = SmallCircuit {}.compile_to_indexes().unwrap().1;
        let vi = &vi.index;
        let x = Fp::from(8u64);
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

        // ft_eval0 constant-term column values
        let mut col_vals = HashMap::new();
        for t in &vi.linearization.constant_term {
            if let PolishToken::Cell(v) = t {
                let pe = combined.evaluate(v.col).unwrap();
                col_vals.insert((v.col, false), pe.zeta);
                col_vals.insert((v.col, true), pe.zeta_omega);
            }
        }
        let srs_log2 = u64::BITS - 1 - (vi.max_poly_size as u64).leading_zeros();

        // fr-sponge column captures
        let e = &proof.evals;
        let pair = |p: &PointEvaluations<Vec<Fp>>| (p.zeta.clone(), p.zeta_omega.clone());

        // cip mandatory columns, in kimchi order
        let cip_cols: Vec<(Fp, Fp)> = crate::ipa::mandatory_columns()
            .into_iter()
            .map(|col| {
                let pe = combined.evaluate(col).unwrap();
                (pe.zeta, pe.zeta_omega)
            })
            .collect();

        let (_, endo_r) = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();

        // the raw 128-bit `v_chal` (opaque in RandomOracles) — replay the
        // Fr-sponge out of circuit via the public `squeeze` API, exactly as
        // `challenge()` does (`squeeze(CHALLENGE_LENGTH_IN_LIMBS)`).
        let claimed_xi = {
            use kimchi::plonk_sponge::FrSponge as _;
            let params = Vesta::sponge_params();
            let mut fr = ScalarSponge::from(params);
            fr.absorb(&o.digest);
            let pcd = ScalarSponge::from(params).digest();
            fr.absorb(&pcd);
            fr.absorb(&proof.ft_eval1);
            fr.absorb_multiple(&o.public_evals[0]);
            fr.absorb_multiple(&o.public_evals[1]);
            fr.absorb_evaluations(&proof.evals);
            fr.squeeze(mina_poseidon::sponge::CHALLENGE_LENGTH_IN_LIMBS)
        };

        let circ = FinalizeCircuit {
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
            digest: o.digest,
            ft_eval1: proof.ft_eval1,
            public_evals: o.public_evals.clone(),
            e_z: pair(&e.z),
            generic: pair(&e.generic_selector),
            poseidon: pair(&e.poseidon_selector),
            complete_add: pair(&e.complete_add_selector),
            mul: pair(&e.mul_selector),
            emul: pair(&e.emul_selector),
            endomul_scalar: pair(&e.endomul_scalar_selector),
            e_w: e.w.iter().map(pair).collect(),
            coefficients: e.coefficients.iter().map(pair).collect(),
            e_s: e.s.iter().map(pair).collect(),
            cip_cols,
            claimed_xi,
            endo_r: *endo_r,
        };

        let (mut fpi, fver) = circ.compile_to_indexes().unwrap();
        let (fproof, out) = fpi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        let ((xi_field, r_field), (cip, xi_correct)) = *out.clone();

        assert_eq!(xi_field, oracles.v, "xi (field) matches kimchi");
        assert_eq!(r_field, oracles.u, "r (field) matches kimchi");
        assert_eq!(cip, o.combined_inner_product, "combined inner product matches");
        assert_eq!(xi_correct, Fp::one(), "xi_correct is true");

        fver.verify::<BaseSponge, ScalarSponge>(fproof, (), *out);
    }
}
