//! The deferred PLONK scalar computations
//! (port of `plonk_checks/plonk_checks.ml`, out-of-circuit side).
//!
//! These are the values a pickles verifier re-derives from the challenges
//! and the evaluations of the proof being verified: the permutation scalar
//! of the linearization, the `ft` evaluation at zeta, and the zeta powers.
//!
//! Note: the constant term of kimchi's linearization is taken as an input
//! here; in Rust it can be evaluated directly with kimchi's `PolishToken`
//! machinery (no need for the OCaml's generated `scalars.ml`). The
//! in-circuit variant will reuse kimchi's `ExprOps` abstraction.

use ark_ff::PrimeField;

use crate::composition_types::plonk::Minimal;

/// Index of the first permutation-argument power of alpha in kimchi's
/// linearization (`perm_alpha0` in the OCaml).
pub const PERM_ALPHA0: usize = 21;

/// Number of powers of alpha used by the linearization.
pub const NUM_ALPHA_POWS: usize = 71;

/// The default number of zero-knowledge rows.
pub const ZK_ROWS: usize = 3;

/// An evaluation domain: a `2^log2_size`-th root of unity.
#[derive(Clone, Copy, Debug)]
pub struct Domain<F> {
    pub log2_size: u32,
    pub generator: F,
}

impl<F: PrimeField> Domain<F> {
    pub fn new(log2_size: u32) -> Self {
        let n = 1u64 << log2_size;
        let generator = F::get_root_of_unity(n).expect("domain too large");
        Self {
            log2_size,
            generator,
        }
    }

    pub fn size(&self) -> u64 {
        1 << self.log2_size
    }

    /// `x^n - 1`.
    pub fn vanishing_polynomial(&self, x: F) -> F {
        x.pow([self.size()]) - F::one()
    }
}

/// The precomputed scalars environment (`Scalars.Env` subset needed by
/// [derive_plonk] and [ft_eval0]).
#[derive(Clone, Debug)]
pub struct ScalarsEnv<F> {
    pub alpha_pows: Vec<F>,
    pub zk_polynomial: F,
    /// `omega^{-zk_rows}`.
    pub omega_to_minus_zk_rows: F,
    pub zeta_to_n_minus_1: F,
    /// `zeta^{2^srs_length_log2}`.
    pub zeta_to_srs_length: F,
    pub beta: F,
    pub gamma: F,
    pub zeta: F,
}

impl<F: PrimeField> ScalarsEnv<F> {
    pub fn alpha_pow(&self, i: usize) -> F {
        self.alpha_pows[i]
    }
}

/// Builds the scalars environment from the minimal challenges
/// (`scalars_env`, with `zk_rows = 3`). `alpha` and `zeta` in `minimal` are
/// scalar challenges; `endo_scalar` interprets them into full field elements.
pub fn scalars_env<F: PrimeField, Bool>(
    domain: &Domain<F>,
    srs_length_log2: u32,
    minimal: &Minimal<F, F, Bool>,
) -> ScalarsEnv<F> {
    let alpha = minimal.alpha;
    let zeta = minimal.zeta;

    let mut alpha_pows = vec![F::one(); NUM_ALPHA_POWS];
    alpha_pows[1] = alpha;
    for i in 2..NUM_ALPHA_POWS {
        alpha_pows[i] = alpha * alpha_pows[i - 1];
    }

    let omega_to_minus_1 = domain.generator.inverse().unwrap();
    // zk_rows = 3: omega^{-2} and omega^{-3}
    let omega_to_zk_plus_1 = omega_to_minus_1.square();
    let omega_to_zk = omega_to_zk_plus_1 * omega_to_minus_1;

    // vanishing polynomial of {omega^-1, omega^-2, omega^-3} at zeta
    let zk_polynomial =
        (zeta - omega_to_minus_1) * (zeta - omega_to_zk_plus_1) * (zeta - omega_to_zk);

    ScalarsEnv {
        alpha_pows,
        zk_polynomial,
        omega_to_minus_zk_rows: omega_to_zk,
        zeta_to_n_minus_1: domain.vanishing_polynomial(zeta),
        zeta_to_srs_length: zeta.pow([1u64 << srs_length_log2]),
        beta: minimal.beta,
        gamma: minimal.gamma,
        zeta,
    }
}

/// The relevant proof evaluations, at `zeta` and `zeta * omega`.
#[derive(Clone, Debug)]
pub struct Evals<F> {
    /// The 15 witness columns, `(at_zeta, at_zeta_omega)`.
    pub w: Vec<(F, F)>,
    /// The first 6 permutation sigmas, `(at_zeta, at_zeta_omega)`.
    pub s: Vec<(F, F)>,
    /// The permutation aggregation, `(at_zeta, at_zeta_omega)`.
    pub z: (F, F),
}

/// The permutation scalar of the linearization (the `perm` of
/// `derive_plonk`):
/// `- z(zeta omega) * beta * alpha^21 * zkp * prod_i (gamma + beta s_i + w_i)`.
pub fn perm_scalar<F: PrimeField>(env: &ScalarsEnv<F>, e: &Evals<F>) -> F {
    let mut acc = e.z.1 * env.beta * env.alpha_pow(PERM_ALPHA0) * env.zk_polynomial;
    for (i, (s, _)) in e.s.iter().enumerate() {
        acc *= env.gamma + (env.beta * s) + e.w[i].0;
    }
    -acc
}

/// `ft_eval0`, the evaluation at zeta of the part of `ft` the verifier
/// recomputes. `p_eval0` is the public-input polynomial evaluated at zeta
/// (in SRS-length chunks), and `constant_term` is kimchi's linearization
/// constant term evaluated on the same environment.
pub fn ft_eval0<F: PrimeField>(
    env: &ScalarsEnv<F>,
    shifts: &[F],
    e: &Evals<F>,
    p_eval0: &[F],
    constant_term: F,
) -> F {
    let zkp = env.zk_polynomial;
    let zeta1m1 = env.zeta_to_n_minus_1;
    let (beta, gamma, zeta) = (env.beta, env.gamma, env.zeta);

    // combine the public-eval chunks by powers of zeta^{srs_length}
    let p_eval0 = p_eval0
        .iter()
        .rev()
        .copied()
        .reduce(|acc, chunk| chunk + env.zeta_to_srs_length * acc)
        .expect("empty public evals");

    let w0: Vec<F> = e.w.iter().map(|(z, _)| *z).collect();

    let mut ft_eval0 = {
        let a0 = env.alpha_pow(PERM_ALPHA0);
        let w_n = w0[e.s.len()]; // PERMUTS - 1 = 6
        let mut acc = (w_n + gamma) * e.z.1 * a0 * zkp;
        for (i, (s, _)) in e.s.iter().enumerate() {
            acc *= (beta * s) + w0[i] + gamma;
        }
        acc
    };

    ft_eval0 -= p_eval0;

    ft_eval0 -= {
        let mut acc = env.alpha_pow(PERM_ALPHA0) * zkp * e.z.0;
        for (i, s) in shifts.iter().enumerate() {
            acc *= gamma + (beta * zeta * s) + w0[i];
        }
        acc
    };

    let nominator =
        ((zeta1m1 * env.alpha_pow(PERM_ALPHA0 + 1) * (zeta - env.omega_to_minus_zk_rows))
            + (zeta1m1 * env.alpha_pow(PERM_ALPHA0 + 2) * (zeta - F::one())))
            * (F::one() - e.z.0);
    let denominator = (zeta - env.omega_to_minus_zk_rows) * (zeta - F::one());
    ft_eval0 += nominator * denominator.inverse().unwrap();

    ft_eval0 - constant_term
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{composition_types::Features, scalar_challenge::ScalarChallenge};
    use ark_ff::Field;
    use mina_curves::pasta::Fp;

    #[test]
    fn scalars_env_basics() {
        use ark_ff::UniformRand;
        let mut rng = o1_utils::tests::make_test_rng(None);
        let domain = Domain::<Fp>::new(5);
        // generator^n = 1
        assert_eq!(domain.generator.pow([domain.size()]), Fp::from(1u64));

        let (_, endo) = <mina_curves::pasta::Vesta as kimchi::curve::KimchiCurve<
            { snarky::FULL_ROUNDS },
        >>::endos();
        let alpha = ScalarChallenge(Fp::from(u128::rand(&mut rng))).to_field(*endo);
        let zeta = ScalarChallenge(Fp::from(u128::rand(&mut rng))).to_field(*endo);
        let minimal = Minimal::<Fp, Fp, bool> {
            alpha,
            beta: Fp::rand(&mut rng),
            gamma: Fp::rand(&mut rng),
            zeta,
            joint_combiner: None,
            feature_flags: Features::none(),
        };
        let env = scalars_env::<Fp, bool>(&domain, 16, &minimal);
        assert_eq!(env.alpha_pows[3], alpha * alpha * alpha);

        // zk_polynomial vanishes on the last three rows
        let omega_inv = domain.generator.inverse().unwrap();
        for k in 1..=3u64 {
            let x = omega_inv.pow([k]);
            let z =
                (x - omega_inv) * (x - omega_inv.square()) * (x - omega_inv.square() * omega_inv);
            assert_eq!(z, Fp::from(0u64));
        }

        // zeta_to_n_minus_1 = zeta^n - 1
        assert_eq!(
            env.zeta_to_n_minus_1,
            env.zeta.pow([domain.size()]) - Fp::from(1u64)
        );
    }
}

#[cfg(test)]
mod oracles_parity_tests {
    use super::*;
    use crate::composition_types::Features;
    use ark_ff::{One, Zero};
    use ark_poly::Polynomial;
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
            // x * x = z, plus a poseidon row to exercise more alphas
            let x: FieldVar<Fp> = sys.compute(loc!(), |_| *private.unwrap())?;
            let xx = x.mul(&x, None, loc!(), sys)?;
            xx.assert_equals(sys, loc!(), &z)?;
            let _ = sys.poseidon(loc!(), (x, z));
            Ok(())
        }
    }

    /// Our scalars_env + ft_eval0 recompute exactly kimchi's
    /// OraclesResult.ft_eval0 on a real proof.
    #[test]
    fn ft_eval0_matches_kimchi_oracles() {
        let circuit = SmallCircuit {};
        let (mut prover_index, verifier_index) = circuit.compile_to_indexes().unwrap();

        let x = Fp::from(7u64);
        let z = x * x;
        let (proof, _) = prover_index
            .prove::<BaseSponge, ScalarSponge>(z, x, true)
            .unwrap();

        let vi = &verifier_index.index;
        let public_input = vec![z];

        // public commitment, as the kimchi verifier builds it
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

        // ==== recompute ft_eval0 with our port ====
        let oracles = &o.oracles;
        let domain = Domain::<Fp> {
            log2_size: vi.domain.log_size_of_group,
            generator: vi.domain.group_gen,
        };
        let srs_length_log2 = u64::BITS - 1 - (vi.max_poly_size as u64).leading_zeros();
        assert_eq!(1usize << srs_length_log2, vi.max_poly_size);

        let minimal = Minimal::<Fp, Fp, bool> {
            alpha: oracles.alpha,
            beta: oracles.beta,
            gamma: oracles.gamma,
            zeta: oracles.zeta,
            joint_combiner: None,
            feature_flags: Features::none(),
        };
        let env = scalars_env::<Fp, bool>(&domain, srs_length_log2, &minimal);

        // sanity: our env matches kimchi's intermediate values
        assert_eq!(env.zeta_to_n_minus_1, o.zeta1 - Fp::one());
        assert_eq!(
            env.zk_polynomial,
            vi.permutation_vanishing_polynomial_m()
                .evaluate(&oracles.zeta)
        );

        // combined evaluations at (zeta, zeta * omega)
        let evals = proof.evals.combine(&o.powers_of_eval_points_for_chunks);
        let e = Evals {
            w: evals.w.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
            s: evals.s.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
            z: (evals.z.zeta, evals.z.zeta_omega),
        };

        // the linearization constant term, straight from kimchi
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
            &evals,
            &constants,
            &challenges,
        )
        .unwrap();

        let ours = ft_eval0(&env, &vi.shift, &e, &o.public_evals[0], constant_term);

        assert_eq!(ours, o.ft_eval0, "ft_eval0 parity with kimchi's verifier");
    }
}
