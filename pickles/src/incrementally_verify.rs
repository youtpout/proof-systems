//! Assembly of pickles' `incrementally_verify_proof` (`wrap_verifier.ml`,
//! lines ~828–1438) — the Fq-side heart of the step/wrap verifier.
//!
//! This threads a single base-field sponge through the Fiat-Shamir transcript,
//! re-deriving the oracles (`beta`, `gamma`, `alpha`, `zeta`), then forks the
//! sponge and runs the bulletproof / inner-product-argument check on the
//! forked copy — exactly as the OCaml does (the fork is
//! `sponge_before_evaluations`, taken right after `zeta` is squeezed).
//!
//! It reuses the already-parity-tested bricks:
//! [`crate::oracles::absorb_commitment`], [`crate::challenge::squeeze_challenge`],
//! [`crate::scalar_challenge::scalar_to_field`], [`crate::commitments::ft_comm`],
//! [`crate::bulletproof::combine_commitments`],
//! [`crate::bulletproof::ipa_challenges_transcript`],
//! [`crate::bulletproof::bullet_reduce_terms`] and
//! [`crate::bulletproof::check_bulletproof_equation`].
//!
//! This is the base subset: no lookups, no optional gates, one chunk per
//! column. The commitment list fed to the polyscale combination follows the
//! `without_degree_bound` order of `wrap_verifier.ml` (lines 1360–1388):
//!
//! ```text
//! sg_old, x_hat, ft_comm, z_comm,
//! generic, poseidon(psm), complete_add, mul(varbase), emul, endomul_scalar,
//! w_comm[15], coefficients_comm[15], sigma_comm[0..PERMUTS-1]
//! ```

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{gadgets::curve::Point, Boolean, FieldVar, RunState, SnarkyResult};

use crate::bulletproof::{
    bullet_reduce_terms, check_bulletproof_equation, combine_commitments, ipa_challenges_transcript,
};
use crate::challenge::squeeze_challenge;
use crate::commitments::ft_comm;
use crate::oracles::{absorb_commitment, FqOracles, PointVar};
use crate::scalar_challenge::scalar_to_field;
use crate::sponge::PoseidonSponge;

/// The verification-key commitments the base step/wrap verifier absorbs and
/// combines (a subset of `Plonk_verification_key_evals.Step.t`, no optional
/// gate commitments). Each is a single chunk (a `Point`).
pub struct VerificationKeyComm<F: PrimeField> {
    pub generic: Point<F>,
    pub psm: Point<F>,
    pub complete_add: Point<F>,
    pub mul: Point<F>,
    pub emul: Point<F>,
    pub endomul_scalar: Point<F>,
    /// The 15 coefficient commitments.
    pub coefficients: Vec<Point<F>>,
    /// The first `PERMUTS-1` (= 6) sigma commitments, combined by the polyscale.
    pub sigma_init: Vec<Point<F>>,
    /// The last (`PERMUTS-1` index) sigma commitment, used by `ft_comm`.
    pub sigma_last: Vec<Point<F>>,
}

/// The proof messages absorbed by the Fq-sponge (base subset): witness,
/// permutation and quotient commitments, each given as its chunks.
pub struct Messages<F: PrimeField> {
    /// The 15 witness column commitments.
    pub w_comm: Vec<Vec<Point<F>>>,
    pub z_comm: Vec<Point<F>>,
    /// The quotient commitment (7 chunks).
    pub t_comm: Vec<Point<F>>,
}

/// The IPA opening proof pieces (`Openings.Bulletproof.t`), plus the SRS
/// blinding generator `H`.
pub struct OpeningProof<F: PrimeField> {
    /// The per-round `(L, R)` commitments.
    pub lr: Vec<(Point<F>, Point<F>)>,
    pub delta: Point<F>,
    /// `Shifted_value.Type1` of `z_1`.
    pub z1: FieldVar<F>,
    /// `Shifted_value.Type1` of `z_2`.
    pub z2: FieldVar<F>,
    /// The challenge-polynomial commitment (`sg`).
    pub challenge_polynomial_commitment: Point<F>,
    /// The SRS blinding generator `H`.
    pub h_generator: Point<F>,
}

/// The deferred scalar advice consumed by the Fq-side verifier
/// (`Shifted_value.Type1` field images): the combined inner product, `b`, and
/// the `ft_comm` PlonK scalars `perm`, `zeta_to_srs_length`,
/// `zeta_to_domain_size`.
pub struct Advice<F: PrimeField> {
    pub combined_inner_product: FieldVar<F>,
    pub b: FieldVar<F>,
    pub perm: FieldVar<F>,
    pub zeta_to_srs_length: FieldVar<F>,
    pub zeta_to_domain_size: FieldVar<F>,
}

/// The output of [`incrementally_verify_proof`].
pub struct IncrementalResult<F: PrimeField> {
    /// The `equal_g` success boolean of the bulletproof equation.
    pub success: Boolean<F>,
    /// The re-derived Fq-sponge oracles.
    pub oracles: FqOracles<F>,
    /// `sponge_digest_before_evaluations` (fed to the Fr-sponge / finalize).
    pub sponge_digest: FieldVar<F>,
    /// The bulletproof round prechallenges (raw 128-bit), recorded as the
    /// deferred `bulletproof_challenges`.
    pub bulletproof_challenges: Vec<FieldVar<F>>,
}

fn to_pv<F: PrimeField>(p: &Point<F>) -> PointVar<F> {
    (p.x.clone(), p.y.clone())
}

fn to_pvs<F: PrimeField>(ps: &[Point<F>]) -> Vec<PointVar<F>> {
    ps.iter().map(to_pv).collect()
}

/// Assembles `incrementally_verify_proof` for the base step/wrap circuit.
///
/// `vk_digest` is the base-field digest of the verifier index (`index.digest`,
/// computed by the caller); `sg_old` are the previous proofs' challenge-
/// polynomial commitments (absorbed as `PC`); `x_hat` is the (blinded) public-
/// input commitment chunks; `xi` is the polyscale challenge (raw 128-bit).
///
/// Two distinct endomorphism constants are needed:
/// - `challenge_endo`: the step field's own scalar endomorphism, used by
///   [`scalar_to_field`] to turn the `alpha`/`zeta` challenges into field
///   elements (`<StepCurve>::endos().1`);
/// - `endo_base`: the inner curve's base-field endomorphism coefficient for the
///   `EndoMul` gate ([`crate::endo::tick::base`] = `<InnerCurve>::endos().0`),
///   used by `combine_commitments`, `endo`, `endo_inv` and the final equation;
/// - `endo_scalar`: the inner curve's scalar-field endomorphism root
///   (`<InnerCurve>::endos().1`), used by the `bullet_reduce` inverse.
///
/// `num_bits` is the other field's `size_in_bits`.
#[allow(clippy::too_many_arguments)]
pub fn incrementally_verify_proof<F, C>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    vk_digest: &FieldVar<F>,
    vk: &VerificationKeyComm<F>,
    sg_old: &[Point<F>],
    x_hat: &[Point<F>],
    messages: &Messages<F>,
    openings: &OpeningProof<F>,
    advice: &Advice<F>,
    xi: &FieldVar<F>,
    group_map_params: &groupmap::BWParameters<C>,
    challenge_endo: F,
    endo_base: F,
    endo_scalar: <ark_ec::short_weierstrass::Affine<C> as ark_ec::AffineRepr>::ScalarField,
    num_bits: usize,
) -> SnarkyResult<IncrementalResult<F>>
where
    F: PrimeField,
    C: ark_ec::short_weierstrass::SWCurveConfig<BaseField = F>,
{
    let mut sponge = PoseidonSponge::new();

    // == IVC Steps 1-2: absorb the verifier-index digest, then sg_old (PC) ==
    sponge.absorb(sys, loc.clone(), std::slice::from_ref(vk_digest));
    for sg in sg_old {
        absorb_commitment(sys, loc.clone(), &mut sponge, &[to_pv(sg)]);
    }

    // == IVC Steps 3-5: absorb x_hat, then the witness commitments ==
    absorb_commitment(sys, loc.clone(), &mut sponge, &to_pvs(x_hat));
    for w in &messages.w_comm {
        absorb_commitment(sys, loc.clone(), &mut sponge, &to_pvs(w));
    }

    // == IVC Step 7: beta, gamma (raw 128-bit) ==
    let beta = squeeze_challenge(sys, loc.clone(), &mut sponge)?;
    let gamma = squeeze_challenge(sys, loc.clone(), &mut sponge)?;

    // == IVC Steps 9-10: absorb z_comm, sample alpha (endo) ==
    absorb_commitment(sys, loc.clone(), &mut sponge, &to_pvs(&messages.z_comm));
    let alpha_chal = squeeze_challenge(sys, loc.clone(), &mut sponge)?;
    let alpha = scalar_to_field(sys, loc.clone(), &alpha_chal, challenge_endo)?;

    // == IVC Steps 11-12: absorb t_comm, sample zeta (endo) ==
    absorb_commitment(sys, loc.clone(), &mut sponge, &to_pvs(&messages.t_comm));
    let zeta_chal = squeeze_challenge(sys, loc.clone(), &mut sponge)?;
    let zeta = scalar_to_field(sys, loc.clone(), &zeta_chal, challenge_endo)?;

    // == IVC Step 13: fork the sponge, then squeeze the digest ==
    // `sponge_before_evaluations` continues into the IPA transcript; the digest
    // is squeezed from the same post-zeta state and fed to the Fr-sponge.
    let mut sponge_before_evaluations = sponge.clone();
    let sponge_digest = sponge.squeeze(sys, loc.clone());

    // == IVC Step 14: ft_comm (linearization commitment) ==
    let ft = ft_comm(
        sys,
        loc.clone(),
        &vk.sigma_last,
        &messages.t_comm,
        &advice.perm,
        &advice.zeta_to_srs_length,
        &advice.zeta_to_domain_size,
        num_bits,
    )?;

    // == IVC Step 15: combine the commitments by xi (Split_commitments.combine) ==
    // without_degree_bound order (wrap_verifier.ml:1360-1388), base/no-lookup.
    let mut commitments: Vec<Point<F>> = Vec::new();
    commitments.extend(sg_old.iter().cloned());
    commitments.extend(x_hat.iter().cloned());
    commitments.push(ft);
    commitments.extend(messages.z_comm.iter().cloned());
    commitments.push(vk.generic.clone());
    commitments.push(vk.psm.clone());
    commitments.push(vk.complete_add.clone());
    commitments.push(vk.mul.clone());
    commitments.push(vk.emul.clone());
    commitments.push(vk.endomul_scalar.clone());
    for w in &messages.w_comm {
        commitments.extend(w.iter().cloned());
    }
    commitments.extend(vk.coefficients.iter().cloned());
    commitments.extend(vk.sigma_init.iter().cloned());

    let combined_polynomial = combine_commitments(sys, loc.clone(), &commitments, xi, endo_base)?;

    // IPA transcript on the forked sponge: absorb_shifted(cip) -> u=group_map ->
    // per-round absorb(L,R)+squeeze prechallenge -> absorb(delta) -> c.
    let lr_pv: Vec<(PointVar<F>, PointVar<F>)> = openings
        .lr
        .iter()
        .map(|(l, r)| (to_pv(l), to_pv(r)))
        .collect();
    let (u, prechallenges, c) = ipa_challenges_transcript::<F, C>(
        sys,
        loc.clone(),
        &mut sponge_before_evaluations,
        &advice.combined_inner_product,
        &lr_pv,
        &to_pv(&openings.delta),
        group_map_params,
    )?;

    // The elliptic-curve fold of the bullet reduction (pre_i^{-1}·L + pre_i·R).
    let lr_prod = bullet_reduce_terms::<F, C>(
        sys,
        loc.clone(),
        &openings.lr,
        &prechallenges,
        endo_base,
        endo_scalar,
    )?;

    // == The final inner-product-argument equation ==
    let success = check_bulletproof_equation(
        sys,
        loc,
        &combined_polynomial,
        &lr_prod,
        &u,
        &advice.combined_inner_product,
        &advice.b,
        &openings.z1,
        &openings.z2,
        &c,
        &openings.delta,
        &openings.challenge_polynomial_commitment,
        &openings.h_generator,
        endo_base,
        num_bits,
    )?;

    Ok(IncrementalResult {
        success,
        oracles: FqOracles {
            beta,
            gamma,
            alpha,
            zeta,
        },
        sponge_digest,
        bulletproof_challenges: prechallenges,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::{AdditiveGroup, BigInteger, One, UniformRand, Zero};
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Fq, Pallas, PallasParameters, Vesta, VestaParameters};
    use mina_poseidon::poseidon::{ArithmeticSponge, Sponge as _};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof as IpaProof;
    use snarky::{api::SnarkyCircuit, loc};

    type BaseSponge =
        DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;
    type RefSponge = ArithmeticSponge<Fp, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    fn lowest_128(x: Fp) -> Fp {
        let bits = x.into_bigint().to_bits_le();
        let mut acc = Fp::zero();
        for &b in bits[..128].iter().rev() {
            acc.double_in_place();
            if b {
                acc += Fp::one();
            }
        }
        acc
    }

    fn rand_pt(rng: &mut impl rand::Rng) -> Pallas {
        (Pallas::generator() * Fq::rand(rng)).into_affine()
    }

    const NUM_BITS: usize = 255;

    /// A self-contained circuit running the whole `incrementally_verify_proof`
    /// over random (non-satisfying) commitment data. This validates that all
    /// the Fq-side bricks compose into a single circuit that compiles, proves
    /// and verifies, and exposes the re-derived `beta`/`gamma` oracles so the
    /// sponge threading (including `sg_old`) can be checked against an
    /// out-of-circuit mirror. The `equal_g` success value is *not* asserted —
    /// it is only satisfiable with a real pickles statement (different
    /// linearization split from kimchi), which lands with the prover (step_main).
    struct IvpCircuit {
        vk_digest: Fp,
        sg_old: Vec<(Fp, Fp)>,
        x_hat: Vec<(Fp, Fp)>,
        w_comm: Vec<Vec<(Fp, Fp)>>,
        z_comm: Vec<(Fp, Fp)>,
        t_comm: Vec<(Fp, Fp)>,
        generic: (Fp, Fp),
        psm: (Fp, Fp),
        complete_add: (Fp, Fp),
        mul: (Fp, Fp),
        emul: (Fp, Fp),
        endomul_scalar: (Fp, Fp),
        coefficients: Vec<(Fp, Fp)>,
        sigma_init: Vec<(Fp, Fp)>,
        sigma_last: Vec<(Fp, Fp)>,
        lr: Vec<((Fp, Fp), (Fp, Fp))>,
        delta: (Fp, Fp),
        cpc: (Fp, Fp),
        h: (Fp, Fp),
        xi: u128,
        cip: u128,
        b: u128,
        z1: u128,
        z2: u128,
        perm: u128,
        zeta_to_srs_length: u128,
        zeta_to_domain_size: u128,
        challenge_endo: Fp,
    }

    impl SnarkyCircuit for IvpCircuit {
        type Curve = Vesta;
        type Proof = IpaProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        // (beta, gamma) exposed for the sponge-order check.
        type PublicOutput = (FieldVar<Fp>, FieldVar<Fp>);
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let mkpt = |sys: &mut RunState<Fp>, p: (Fp, Fp)| -> SnarkyResult<Point<Fp>> {
                Ok(Point::new(
                    sys.compute(loc!(), move |_| p.0)?,
                    sys.compute(loc!(), move |_| p.1)?,
                ))
            };
            let mkpts = |sys: &mut RunState<Fp>, ps: &[(Fp, Fp)]| -> SnarkyResult<Vec<Point<Fp>>> {
                let mut out = vec![];
                for &p in ps {
                    out.push(mkpt(sys, p)?);
                }
                Ok(out)
            };
            let mksc = |sys: &mut RunState<Fp>, s: u128| sys.compute(loc!(), move |_| Fp::from(s));

            let vk_digest: FieldVar<Fp> = sys.compute(loc!(), |_| self.vk_digest)?;
            let sg_old = mkpts(sys, &self.sg_old)?;
            let x_hat = mkpts(sys, &self.x_hat)?;
            let mut w_comm = vec![];
            for w in &self.w_comm {
                w_comm.push(mkpts(sys, w)?);
            }
            let z_comm = mkpts(sys, &self.z_comm)?;
            let t_comm = mkpts(sys, &self.t_comm)?;
            let vk = VerificationKeyComm {
                generic: mkpt(sys, self.generic)?,
                psm: mkpt(sys, self.psm)?,
                complete_add: mkpt(sys, self.complete_add)?,
                mul: mkpt(sys, self.mul)?,
                emul: mkpt(sys, self.emul)?,
                endomul_scalar: mkpt(sys, self.endomul_scalar)?,
                coefficients: mkpts(sys, &self.coefficients)?,
                sigma_init: mkpts(sys, &self.sigma_init)?,
                sigma_last: mkpts(sys, &self.sigma_last)?,
            };
            let messages = Messages {
                w_comm,
                z_comm,
                t_comm,
            };
            let mut lr = vec![];
            for &(l, r) in &self.lr {
                lr.push((mkpt(sys, l)?, mkpt(sys, r)?));
            }
            let openings = OpeningProof {
                lr,
                delta: mkpt(sys, self.delta)?,
                z1: mksc(sys, self.z1)?,
                z2: mksc(sys, self.z2)?,
                challenge_polynomial_commitment: mkpt(sys, self.cpc)?,
                h_generator: mkpt(sys, self.h)?,
            };
            let advice = Advice {
                combined_inner_product: mksc(sys, self.cip)?,
                b: mksc(sys, self.b)?,
                perm: mksc(sys, self.perm)?,
                zeta_to_srs_length: mksc(sys, self.zeta_to_srs_length)?,
                zeta_to_domain_size: mksc(sys, self.zeta_to_domain_size)?,
            };
            let xi = mksc(sys, self.xi)?;

            use groupmap::GroupMap;
            let params = groupmap::BWParameters::<PallasParameters>::setup();
            let res = incrementally_verify_proof::<Fp, PallasParameters>(
                sys,
                loc!(),
                &vk_digest,
                &vk,
                &sg_old,
                &x_hat,
                &messages,
                &openings,
                &advice,
                &xi,
                &params,
                self.challenge_endo,
                crate::endo::tick::base(),
                <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1,
                NUM_BITS,
            )?;
            // seal the success boolean so it can be dropped without wiring issues
            let _ = res.success;
            Ok((res.oracles.beta, res.oracles.gamma))
        }
    }

    /// Out-of-circuit mirror of the oracle sponge (vk_digest, sg_old, x_hat,
    /// w_comm, then squeeze beta, gamma) over a plain `ArithmeticSponge<Fp>`.
    #[allow(clippy::too_many_arguments)]
    fn reference_beta_gamma(
        vk_digest: Fp,
        sg_old: &[(Fp, Fp)],
        x_hat: &[(Fp, Fp)],
        w_comm: &[Vec<(Fp, Fp)>],
    ) -> (Fp, Fp) {
        let mut s = RefSponge::new(Vesta::sponge_params());
        let absorb_c = |s: &mut RefSponge, chunks: &[(Fp, Fp)]| {
            for (x, y) in chunks {
                s.absorb(&[*x]);
                s.absorb(&[*y]);
            }
        };
        s.absorb(&[vk_digest]);
        for sg in sg_old {
            absorb_c(&mut s, std::slice::from_ref(sg));
        }
        absorb_c(&mut s, x_hat);
        for w in w_comm {
            absorb_c(&mut s, w);
        }
        (lowest_128(s.squeeze()), lowest_128(s.squeeze()))
    }

    /// The full `incrementally_verify_proof` circuit compiles, proves and
    /// verifies, and its re-derived `beta`/`gamma` match the out-of-circuit
    /// sponge (validating the transcript order including `sg_old`).
    #[test]
    fn incrementally_verify_proof_assembles_and_matches_oracles() {
        let mut rng = o1_utils::tests::make_test_rng(None);
        let pt = |rng: &mut _| {
            let p = rand_pt(rng);
            (p.x, p.y)
        };
        let (_, endo_r) = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();

        let sg_old = vec![pt(&mut rng)];
        let x_hat = vec![pt(&mut rng)];
        let w_comm: Vec<Vec<(Fp, Fp)>> = (0..15).map(|_| vec![pt(&mut rng)]).collect();
        let z_comm = vec![pt(&mut rng)];
        let t_comm: Vec<(Fp, Fp)> = (0..7).map(|_| pt(&mut rng)).collect();
        let coefficients: Vec<(Fp, Fp)> = (0..15).map(|_| pt(&mut rng)).collect();
        let sigma_init: Vec<(Fp, Fp)> = (0..6).map(|_| pt(&mut rng)).collect();
        let sigma_last = vec![pt(&mut rng)];
        let lr: Vec<((Fp, Fp), (Fp, Fp))> = (0..2).map(|_| (pt(&mut rng), pt(&mut rng))).collect();

        let (beta_ref, gamma_ref) = reference_beta_gamma(
            {
                // vk_digest below must match the circuit's field
                Fp::from(7u64)
            },
            &sg_old,
            &x_hat,
            &w_comm,
        );

        let circ = IvpCircuit {
            vk_digest: Fp::from(7u64),
            sg_old,
            x_hat,
            w_comm,
            z_comm,
            t_comm,
            generic: pt(&mut rng),
            psm: pt(&mut rng),
            complete_add: pt(&mut rng),
            mul: pt(&mut rng),
            emul: pt(&mut rng),
            endomul_scalar: pt(&mut rng),
            coefficients,
            sigma_init,
            sigma_last,
            lr,
            delta: pt(&mut rng),
            cpc: pt(&mut rng),
            h: pt(&mut rng),
            xi: u128::rand(&mut rng),
            cip: u128::rand(&mut rng),
            b: u128::rand(&mut rng),
            z1: u128::rand(&mut rng),
            z2: u128::rand(&mut rng),
            perm: u128::rand(&mut rng),
            zeta_to_srs_length: u128::rand(&mut rng),
            zeta_to_domain_size: u128::rand(&mut rng),
            challenge_endo: *endo_r,
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        let (beta, gamma) = *out.clone();
        assert_eq!(beta, beta_ref, "beta (sponge order incl. sg_old)");
        assert_eq!(gamma, gamma_ref, "gamma");
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }
}
