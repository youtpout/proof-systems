//! Out-of-circuit computation of the wrap proof's deferred values (pickles'
//! `wrap_deferred_values.ml::expand_deferred`).
//!
//! This is the *prover-side* counterpart of the in-circuit
//! [`crate::finalize`]: given a step proof's evaluations and Fiat-Shamir
//! challenges, it recomputes the deferred scalars that get stored in the wrap
//! statement — `combined_inner_product`, `b`, the permutation scalar `perm`,
//! and the field images of the bulletproof challenges. The in-circuit
//! `finalize_other_proof` later re-derives the same values and checks the
//! stored ones against them.
//!
//! `combined_inner_product` and `b` are stored in `Shifted_value.Type1` form
//! (see [`crate::shifted_value`]) so they can be fed straight to `scale_fast`.

use ark_ff::PrimeField;
use kimchi::proof::{PointEvaluations, ProofEvaluations};

use crate::{
    composition_types::BulletproofChallenge,
    ipa::{challenge_polynomial, combined_inner_product, compute_challenges},
    plonk_checks::{perm_scalar, Evals, ScalarsEnv},
    scalar_challenge::ScalarChallenge,
    shifted_value::type1_of_field,
};

/// The deferred values recomputed by the prover for the wrap statement (base
/// subset: the fields the in-circuit `finalize_other_proof` checks).
pub struct DeferredValues<F> {
    /// `Shifted_value.Type1` of the actual combined inner product.
    pub combined_inner_product: F,
    /// `Shifted_value.Type1` of `b = h(ζ) + r·h(ζω)`.
    pub b: F,
    /// `Shifted_value.Type1` of the permutation scalar `perm` (the only scalar
    /// `Plonk_checks.checked` defers, recovered in `finalize` via `shift1`).
    pub perm: F,
    /// The bulletproof challenges as field images (`Ipa.Step.compute_challenges`).
    pub bulletproof_challenges: Vec<F>,
}

/// Recompute the deferred values from a step proof's evaluations and
/// challenges (`expand_deferred`), in the base case (no recursively-verified
/// proofs, so `sg_olds` is empty). `xi`/`r` are the Fr-sponge outputs
/// (`oracles.v`/`oracles.u`); `env`/`evals` feed the permutation scalar;
/// `bulletproof_prechallenges` are the raw 128-bit IPA challenges of this proof.
#[allow(clippy::too_many_arguments)]
pub fn expand_deferred<F: PrimeField>(
    xi: F,
    r: F,
    sg_olds: &[(F, F)],
    public_evals: &[Vec<F>; 2],
    ft_eval0: F,
    ft_eval1: F,
    column_evals: &ProofEvaluations<PointEvaluations<Vec<F>>>,
    zeta: F,
    zetaw: F,
    bulletproof_prechallenges: &[BulletproofChallenge<ScalarChallenge<F>>],
    endo: F,
    env: &ScalarsEnv<F>,
    evals: &Evals<F>,
) -> DeferredValues<F> {
    // actual combined inner product (kimchi order, our port)
    let cip_actual = combined_inner_product(
        xi,
        r,
        sg_olds,
        public_evals,
        ft_eval0,
        ft_eval1,
        column_evals,
    );

    // b = h(ζ) + r·h(ζω), h = challenge polynomial of this proof's challenges
    let bulletproof_challenges = compute_challenges(bulletproof_prechallenges, endo);
    let b_actual = challenge_polynomial(&bulletproof_challenges, zeta)
        + r * challenge_polynomial(&bulletproof_challenges, zetaw);

    // the deferred permutation scalar (stored shifted, like cip and b)
    let perm = perm_scalar(env, evals);

    DeferredValues {
        combined_inner_product: type1_of_field(cip_actual),
        b: type1_of_field(b_actual),
        perm: type1_of_field(perm),
        bulletproof_challenges,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        plonk_checks::{ft_eval0, scalars_env, Domain, ZK_ROWS},
        shifted_value::type1_to_field,
    };
    use ark_ff::{One, UniformRand, Zero};
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
        ) -> SnarkyResult<()> {
            let x: FieldVar<Fp> = sys.compute(loc!(), |_| *private.unwrap())?;
            let xx = x.mul(&x, None, loc!(), sys)?;
            xx.assert_equals(sys, loc!(), &z)?;
            let _ = sys.poseidon(loc!(), (x, z));
            Ok(())
        }
    }

    /// `expand_deferred` on a real proof: its (unshifted) combined inner product
    /// equals kimchi's `OraclesResult.combined_inner_product`, and the stored
    /// shifted form round-trips back to it.
    #[test]
    fn expand_deferred_matches_kimchi_cip() {
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
        let combined = proof.evals.combine(&o.powers_of_eval_points_for_chunks);
        let evals = Evals {
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
        let ft_eval0_v = ft_eval0(&env, &vi.shift, &evals, &o.public_evals[0], constant_term);

        let zeta = oracles.zeta;
        let zetaw = zeta * vi.domain.group_gen;
        let mut rng = o1_utils::tests::make_test_rng(None);
        let prechallenges: Vec<BulletproofChallenge<ScalarChallenge<Fp>>> = (0..16)
            .map(|_| BulletproofChallenge {
                prechallenge: ScalarChallenge(Fp::from(u128::rand(&mut rng))),
            })
            .collect();
        let endo_r = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1;

        let dv = expand_deferred(
            oracles.v,
            oracles.u,
            &[],
            &o.public_evals,
            ft_eval0_v,
            proof.ft_eval1,
            &proof.evals,
            zeta,
            zetaw,
            &prechallenges,
            endo_r,
            &env,
            &evals,
        );

        // stored cip is Shifted_value.Type1; recovering it gives kimchi's value
        assert_eq!(
            type1_to_field(dv.combined_inner_product),
            o.combined_inner_product,
            "expand_deferred combined_inner_product"
        );
        // b round-trips through the shift
        let bp = compute_challenges(&prechallenges, endo_r);
        let b_ref = challenge_polynomial(&bp, zeta) + oracles.u * challenge_polynomial(&bp, zetaw);
        assert_eq!(type1_to_field(dv.b), b_ref, "expand_deferred b");
        assert_eq!(dv.bulletproof_challenges, bp, "bulletproof challenges");
    }
}
