//! Inner-product-argument helpers shared by the pickles verifiers
//! (port of the `challenge_polynomial` of `wrap_verifier.ml` and the
//! `Ipa.compute_challenge(s)` of `common.ml`).

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{FieldVar, RunState, SnarkyResult};

use crate::{composition_types::BulletproofChallenge, scalar_challenge::ScalarChallenge};

/// Converts an IPA prechallenge to its field form via the endomorphism
/// (`Ipa.compute_challenge`).
pub fn compute_challenge<F: PrimeField>(
    prechallenge: &BulletproofChallenge<ScalarChallenge<F>>,
    endo_scalar: F,
) -> F {
    prechallenge.prechallenge.to_field(endo_scalar)
}

/// Converts all IPA prechallenges (`Ipa.compute_challenges`).
pub fn compute_challenges<F: PrimeField>(
    prechallenges: &[BulletproofChallenge<ScalarChallenge<F>>],
    endo_scalar: F,
) -> Vec<F> {
    prechallenges
        .iter()
        .map(|c| compute_challenge(c, endo_scalar))
        .collect()
}

/// Evaluates the IPA challenge polynomial
/// `prod_i (1 + chals[i] * pt^{2^{k-1-i}})` out of circuit.
pub fn challenge_polynomial<F: PrimeField>(chals: &[F], pt: F) -> F {
    let k = chals.len();
    // pow_two_pows[i] = pt^{2^i}
    let mut pow_two_pows = vec![pt; k];
    for i in 1..k {
        pow_two_pows[i] = pow_two_pows[i - 1].square();
    }
    let mut res = F::one();
    for (i, c) in chals.iter().enumerate() {
        res *= F::one() + *c * pow_two_pows[k - 1 - i];
    }
    res
}

/// In-circuit evaluation of the IPA challenge polynomial — the core of the
/// `b` check in `finalize_other_proof`.
pub fn challenge_polynomial_circuit<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    chals: &[FieldVar<F>],
    pt: &FieldVar<F>,
) -> SnarkyResult<FieldVar<F>> {
    let k = chals.len();
    // pow_two_pows[i] = pt^{2^i}
    let pow_loc: Cow<'static, str> = Cow::Owned(format!("{loc} | pow"));
    let mut pow_two_pows = vec![pt.clone()];
    for i in 1..k {
        let prev = &pow_two_pows[i - 1];
        pow_two_pows.push(prev.mul(prev, None, pow_loc.clone(), sys)?);
    }
    // product of the terms 1 + chals[i] * pt^{2^{k-1-i}}. OCaml `prod`
    // (step.ml:130) folds `r := f i * !r` — the NEW term is the LEFT operand
    // of each mul, so the reduced product gate has `f(i)` in `l` and the
    // accumulator in `r` (form parity with jsoo's `b_actual`).
    let mut res = FieldVar::constant(F::one());
    for (i, c) in chals.iter().enumerate() {
        let scaled = c.mul(&pow_two_pows[k - 1 - i], None, loc.clone(), sys)?;
        let term = &FieldVar::constant(F::one()) + &scaled;
        res = term.mul(&res, None, loc.clone(), sys)?;
    }
    Ok(res)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::TOCK_ROUNDS;
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;
    use snarky::{api::SnarkyCircuit, loc, RunState};

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    const K: usize = TOCK_ROUNDS;

    struct BPolyCircuit {}

    impl SnarkyCircuit for BPolyCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;

        /// (challenges, evaluation point)
        type PrivateInput = ([Fp; K], Fp);
        type PublicInput = ();
        type PublicOutput = FieldVar<Fp>;

        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _public: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let chals: [FieldVar<Fp>; K] = sys.compute(loc!(), |_| private.unwrap().0)?;
            let pt: FieldVar<Fp> = sys.compute(loc!(), |_| private.unwrap().1)?;
            challenge_polynomial_circuit(sys, loc!(), &chals, &pt)
        }
    }

    /// The in-circuit challenge polynomial equals the out-of-circuit one,
    /// on challenges derived from real prechallenges.
    #[test]
    fn challenge_polynomial_parity() {
        let circuit = BPolyCircuit {};
        let (mut prover_index, verifier_index) = circuit.compile_to_indexes().unwrap();

        let mut rng = o1_utils::tests::make_test_rng(None);
        let (_, endo_scalar) = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();

        use ark_ff::UniformRand;
        // challenges as they would come out of an IPA transcript
        let prechallenges: Vec<_> = (0..K)
            .map(|_| BulletproofChallenge {
                prechallenge: ScalarChallenge(Fp::from(u128::rand(&mut rng))),
            })
            .collect();
        let chals: [Fp; K] = compute_challenges(&prechallenges, *endo_scalar)
            .try_into()
            .unwrap();
        let pt = Fp::rand(&mut rng);

        let expected = challenge_polynomial(&chals, pt);

        let (proof, public_output) = prover_index
            .prove::<BaseSponge, ScalarSponge>((), (chals, pt), true)
            .unwrap();

        assert_eq!(*public_output, expected);
        verifier_index.verify::<BaseSponge, ScalarSponge>(proof, (), *public_output);
    }
}

//
// combined_inner_product (the core of finalize_other_proof step 11)
//

use kimchi::{
    circuits::{
        berkeley_columns::Column,
        gate::GateType,
        wires::{COLUMNS, PERMUTS},
    },
    proof::ProofEvaluations,
};

/// The mandatory columns combined by the inner product, in kimchi's exact
/// order (the no-optional-gate, no-lookup subset used by a base step
/// circuit). Matches the `for col in [...]` iterator of the kimchi verifier.
pub fn mandatory_columns() -> Vec<Column> {
    let mut cols = vec![
        Column::Z,
        Column::Index(GateType::Generic),
        Column::Index(GateType::Poseidon),
        Column::Index(GateType::CompleteAdd),
        Column::Index(GateType::VarBaseMul),
        Column::Index(GateType::EndoMul),
        Column::Index(GateType::EndoMulScalar),
    ];
    cols.extend((0..COLUMNS).map(Column::Witness));
    cols.extend((0..COLUMNS).map(Column::Coefficient));
    cols.extend((0..PERMUTS - 1).map(Column::Permutation));
    cols
}

/// Reconstructs the combined inner product exactly as the pickles verifier
/// does in `finalize_other_proof` (step 11), for the no-optional-gate case:
/// `es = [public_evals, [ft_eval0, ft_eval1], mandatory columns...]`,
/// each entry being `[eval_at_zeta, eval_at_zetaw]`, folded by
/// `combined_inner_product(xi, r, es)`.
///
/// `sg_olds` are the previous-challenge polynomial evaluations (empty for a
/// base proof), which come first in the list.
pub fn combined_inner_product<F: ark_ff::PrimeField>(
    xi: F,
    r: F,
    sg_olds: &[(F, F)],
    public_evals: &[Vec<F>; 2],
    ft_eval0: F,
    ft_eval1: F,
    column_evals: &ProofEvaluations<kimchi::proof::PointEvaluations<Vec<F>>>,
) -> F {
    let mut es: Vec<Vec<Vec<F>>> = sg_olds
        .iter()
        .map(|(z, zw)| vec![vec![*z], vec![*zw]])
        .collect();
    es.push(public_evals.to_vec());
    es.push(vec![vec![ft_eval0], vec![ft_eval1]]);
    for col in mandatory_columns() {
        let e = column_evals
            .get_column(col)
            .expect("missing mandatory column evaluation");
        es.push(vec![e.zeta.clone(), e.zeta_omega.clone()]);
    }
    poly_commitment::commitment::combined_inner_product(&xi, &r, &es)
}

#[cfg(test)]
mod cip_tests {
    use super::*;
    use crate::plonk_checks::{ft_eval0, scalars_env, Domain, Evals, ZK_ROWS};
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
    use snarky::{api::SnarkyCircuit, loc, FieldVar, RunState, SnarkyResult};

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

    /// Our combined_inner_product (fed with our own ft_eval0) equals kimchi's
    /// OraclesResult.combined_inner_product on a real proof.
    #[test]
    fn combined_inner_product_matches_kimchi() {
        let circuit = SmallCircuit {};
        let (mut prover_index, verifier_index) = circuit.compile_to_indexes().unwrap();

        let x = Fp::from(9u64);
        let z = x * x;
        let (proof, _) = prover_index
            .prove::<BaseSponge, ScalarSponge>(z, x, true)
            .unwrap();

        let vi = &verifier_index.index;
        let public_input = vec![z];

        let lgr = vi.srs().get_lagrange_basis(vi.domain);
        let com: Vec<_> = lgr.iter().take(vi.public).collect();
        let elm: Vec<_> = public_input.iter().map(|s| -*s).collect();
        let public_comm = PolyComm::<Vesta>::multi_scalar_mul(&com, &elm);
        let public_comm = vi
            .srs()
            .mask_custom(public_comm.clone(), &public_comm.map(|_| Fp::one()))
            .unwrap()
            .commitment;

        let o = proof
            .oracles::<BaseSponge, ScalarSponge, _>(vi, &public_comm, Some(&public_input))
            .unwrap();
        let oracles = &o.oracles;

        // recompute ft_eval0 with our port
        let domain = Domain::<Fp> {
            log2_size: vi.domain.log_size_of_group,
            generator: vi.domain.group_gen,
        };
        let srs_length_log2 = u64::BITS - 1 - (vi.max_poly_size as u64).leading_zeros();
        let minimal = crate::composition_types::plonk::Minimal::<Fp, Fp, bool> {
            alpha: oracles.alpha,
            beta: oracles.beta,
            gamma: oracles.gamma,
            zeta: oracles.zeta,
            joint_combiner: None,
            feature_flags: crate::composition_types::Features::none(),
        };
        let env = scalars_env::<Fp, bool>(&domain, srs_length_log2, &minimal);
        let combined = proof.evals.combine(&o.powers_of_eval_points_for_chunks);
        let e = Evals {
            w: combined.w.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
            s: combined.s.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
            z: (combined.z.zeta, combined.z.zeta_omega),
        };
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
        let constant_term = PolishToken::evaluate(
            &vi.linearization.constant_term,
            vi.domain,
            oracles.zeta,
            &combined,
            &constants,
            &challenges,
        )
        .unwrap();
        let my_ft_eval0 = ft_eval0(&env, &vi.shift, &e, &o.public_evals[0], constant_term);

        // reconstruct combined_inner_product (base proof: no sg_olds)
        let ours = combined_inner_product(
            oracles.v, // xi (polyscale)
            oracles.u, // r (evalscale)
            &[],
            &o.public_evals,
            my_ft_eval0,
            proof.ft_eval1,
            &proof.evals,
        );

        assert_eq!(ours, o.combined_inner_product);
    }
}

/// In-circuit combined inner product for the single-chunk case (the base
/// step circuit uses `chunk_size = 1`). Each entry is a column's
/// `(eval_at_zeta, eval_at_zetaw)`, taken in kimchi's order; the result is
/// `Σ_i xi^i * (zeta_i + r * zetaw_i)`.
pub fn combined_inner_product_circuit<F: ark_ff::PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    xi: &FieldVar<F>,
    r: &FieldVar<F>,
    entries: &[(FieldVar<F>, FieldVar<F>)],
) -> SnarkyResult<FieldVar<F>> {
    combined_inner_product_circuit_masked(sys, loc, xi, r, &[], entries)
}

/// OCaml `Common.combined_evaluation` (common.ml:216): a Horner fold over one
/// evaluation point, `acc = fx + xi * acc` per entry (`Field.if_` around it
/// for a masked entry, which then consumes no power of xi). Entries are
/// processed back to front so entry 0 pairs with `xi^0`, exactly the value
/// kimchi's `combined_inner_product` computes.
fn combined_evaluation<F: ark_ff::PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    xi: &FieldVar<F>,
    values: &[(Option<snarky::Boolean<F>>, FieldVar<F>)],
) -> SnarkyResult<FieldVar<F>> {
    let mut iter = values.iter().rev();
    let mut acc = match iter.next().expect("combined_evaluation: empty") {
        (None, v) => v.clone(),
        (Some(b), v) => v.mul(&b.to_field_var(), None, loc.clone(), sys)?,
    };
    for (mask, v) in iter {
        let xi_acc = xi.mul(&acc, None, loc.clone(), sys)?;
        let folded = v + &xi_acc;
        acc = match mask {
            None => folded,
            Some(b) => sys.if_(loc.clone(), b.clone(), folded, acc)?,
        };
    }
    Ok(acc)
}

/// Fixed-width `combined_evaluation` with optional prefix entries. For a
/// disabled entry neither its contribution nor its power of `xi` is
/// consumed, matching OCaml's `Opt.Maybe` fold for padded recursion slots.
pub fn combined_inner_product_circuit_masked<F: ark_ff::PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    xi: &FieldVar<F>,
    r: &FieldVar<F>,
    masked_prefix: &[(snarky::Boolean<F>, FieldVar<F>, FieldVar<F>)],
    entries: &[(FieldVar<F>, FieldVar<F>)],
) -> SnarkyResult<FieldVar<F>> {
    // OCaml step 8b: two independent Horner folds — one per evaluation
    // point — then `combine(zeta) + r * combine(zetaw)`
    // (`wrap_verifier.ml:1725-1729`); masked recursion slots fold as
    // `Opt.Maybe` entries at the head of each list.
    let zeta_values: Vec<(Option<snarky::Boolean<F>>, FieldVar<F>)> = masked_prefix
        .iter()
        .map(|(b, zeta, _)| (Some(b.clone()), zeta.clone()))
        .chain(entries.iter().map(|(zeta, _)| (None, zeta.clone())))
        .collect();
    let zetaw_values: Vec<(Option<snarky::Boolean<F>>, FieldVar<F>)> = masked_prefix
        .iter()
        .map(|(b, _, zetaw)| (Some(b.clone()), zetaw.clone()))
        .chain(entries.iter().map(|(_, zetaw)| (None, zetaw.clone())))
        .collect();
    // OCaml `combine(zeta) + r * combine(zetaw)` (step_verifier.ml:1107-1112):
    // the `+`'s operands evaluate RIGHT-TO-LEFT, so the ZETAW fold's gates are
    // emitted before the ZETA fold's.
    let at_zetaw = combined_evaluation(sys, loc.clone(), xi, &zetaw_values)?;
    let r_at_zetaw = r.mul(&at_zetaw, None, loc.clone(), sys)?;
    let at_zeta = combined_evaluation(sys, loc.clone(), xi, &zeta_values)?;
    Ok(&at_zeta + &r_at_zetaw)
}

#[cfg(test)]
mod cip_circuit_tests {
    use super::*;
    use crate::plonk_checks::{ft_eval0, scalars_env, Domain, Evals, ZK_ROWS};
    use ark_ff::{One, Zero};
    use kimchi::{
        circuits::{
            berkeley_columns::BerkeleyChallenges,
            expr::{ColumnEvaluations, Constants, PolishToken},
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
        ) -> SnarkyResult<()> {
            let x: FieldVar<Fp> = sys.compute(loc!(), |_| *private.unwrap())?;
            let xx = x.mul(&x, None, loc!(), sys)?;
            xx.assert_equals(sys, loc!(), &z)?;
            let _ = sys.poseidon(loc!(), (x, z));
            Ok(())
        }
    }

    /// entries as captured (zeta, zetaw) values, replayed in circuit.
    struct CipCircuit {
        xi: Fp,
        r: Fp,
        entries: Vec<(Fp, Fp)>,
    }
    impl SnarkyCircuit for CipCircuit {
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
            let xi: FieldVar<Fp> = sys.compute(loc!(), |_| self.xi)?;
            let r: FieldVar<Fp> = sys.compute(loc!(), |_| self.r)?;
            let mut entries = vec![];
            for &(a, b) in &self.entries {
                let za: FieldVar<Fp> = sys.compute(loc!(), move |_| a)?;
                let zb: FieldVar<Fp> = sys.compute(loc!(), move |_| b)?;
                entries.push((za, zb));
            }
            combined_inner_product_circuit(sys, loc!(), &xi, &r, &entries)
        }
    }

    /// The in-circuit combined_inner_product (fed with our ft_eval0) matches
    /// kimchi's OraclesResult.combined_inner_product on a real proof.
    #[test]
    fn combined_inner_product_circuit_matches_kimchi() {
        let mut pi = SmallCircuit {}.compile_to_indexes().unwrap().0;
        let vi = SmallCircuit {}.compile_to_indexes().unwrap().1;
        let vi = &vi.index;
        let x = Fp::from(4u64);
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

        // our ft_eval0 (out of circuit, already validated)
        let domain = Domain::<Fp> {
            log2_size: vi.domain.log_size_of_group,
            generator: vi.domain.group_gen,
        };
        let srs_log2 = u64::BITS - 1 - (vi.max_poly_size as u64).leading_zeros();
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
        let ct = PolishToken::evaluate(
            &vi.linearization.constant_term,
            vi.domain,
            oracles.zeta,
            &combined,
            &constants,
            &challenges,
        )
        .unwrap();
        let ft0 = ft_eval0(&env, &vi.shift, &e, &o.public_evals[0], ct);

        // build the entries in kimchi's order: public, [ft0, ft1], columns
        let mut entries: Vec<(Fp, Fp)> = vec![];
        entries.push((o.public_evals[0][0], o.public_evals[1][0]));
        entries.push((ft0, proof.ft_eval1));
        for col in mandatory_columns() {
            let pe = combined.evaluate(col).unwrap();
            entries.push((pe.zeta, pe.zeta_omega));
        }

        let circ = CipCircuit {
            xi: oracles.v,
            r: oracles.u,
            entries,
        };
        let (mut cpi, cver) = circ.compile_to_indexes().unwrap();
        let (cproof, out) = cpi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        assert_eq!(*out, o.combined_inner_product);
        cver.verify::<BaseSponge, ScalarSponge>(cproof, (), *out);
    }
}
