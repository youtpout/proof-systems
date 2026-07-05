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
use crate::scalar_challenge::ScalarChallenge;

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
pub fn scalars_env<F: PrimeField, Chal, Bool>(
    domain: &Domain<F>,
    srs_length_log2: u32,
    endo_scalar: F,
    minimal: &Minimal<F, ScalarChallenge<F>, Bool>,
) -> ScalarsEnv<F>
where
    Chal: Clone,
{
    let alpha = minimal.alpha.to_field(endo_scalar);
    let zeta = minimal.zeta.to_field(endo_scalar);

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
    use crate::composition_types::Features;
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
        let minimal = Minimal::<Fp, _, bool> {
            alpha: ScalarChallenge(Fp::from(u128::rand(&mut rng))),
            beta: Fp::rand(&mut rng),
            gamma: Fp::rand(&mut rng),
            zeta: ScalarChallenge(Fp::from(u128::rand(&mut rng))),
            joint_combiner: None,
            feature_flags: Features::none(),
        };
        let env = scalars_env::<Fp, Fp, bool>(&domain, 16, *endo, &minimal);

        // alpha_pows[i] = alpha^i
        let alpha = minimal.alpha.to_field(*endo);
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
