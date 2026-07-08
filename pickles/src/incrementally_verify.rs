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
use crate::plonk_curve_ops::ShiftedScalar;
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
/// blinding generator `H`. The scalars are [`ShiftedScalar`] representatives
/// ([`ShiftedScalar::Type2`] pairs in a step circuit, single
/// [`ShiftedScalar::Type1`] in a wrap circuit).
pub struct OpeningProof<F: PrimeField> {
    /// The per-round `(L, R)` commitments.
    pub lr: Vec<(Point<F>, Point<F>)>,
    pub delta: Point<F>,
    pub z1: ShiftedScalar<F>,
    pub z2: ShiftedScalar<F>,
    /// The challenge-polynomial commitment (`sg`).
    pub challenge_polynomial_commitment: Point<F>,
    /// The SRS blinding generator `H`.
    pub h_generator: Point<F>,
}

/// The deferred scalar advice consumed by the Fq-side verifier
/// ([`ShiftedScalar`] representatives): the combined inner product, `b`, and
/// the `ft_comm` PlonK scalars `perm`, `zeta_to_srs_length`,
/// `zeta_to_domain_size`.
pub struct Advice<F: PrimeField> {
    pub combined_inner_product: ShiftedScalar<F>,
    pub b: ShiftedScalar<F>,
    pub perm: ShiftedScalar<F>,
    pub zeta_to_srs_length: ShiftedScalar<F>,
    pub zeta_to_domain_size: ShiftedScalar<F>,
}

/// The output of [`incrementally_verify_proof`].
pub struct IncrementalResult<F: PrimeField> {
    /// The `equal_g` success boolean of the bulletproof equation.
    pub success: Boolean<F>,
    /// The re-derived Fq-sponge oracles, all as *raw* 128-bit challenges
    /// (alpha/zeta included — the endo `to_field` mapping happens in the other
    /// side's `finalize`, so the caller compares them raw against the
    /// statement's scalar challenges, as OCaml's `assert_eq_plonk` does).
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
/// All four oracles are sampled *raw* (no endo `to_field` — that happens in
/// the other side's `finalize`). Two endomorphism constants are needed:
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

    // == IVC Steps 9-10: absorb z_comm, sample alpha (raw scalar challenge) ==
    absorb_commitment(sys, loc.clone(), &mut sponge, &to_pvs(&messages.z_comm));
    let alpha = squeeze_challenge(sys, loc.clone(), &mut sponge)?;

    // == IVC Steps 11-12: absorb t_comm, sample zeta (raw scalar challenge) ==
    absorb_commitment(sys, loc.clone(), &mut sponge, &to_pvs(&messages.t_comm));
    let zeta = squeeze_challenge(sys, loc.clone(), &mut sponge)?;

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

    /// Splits an Fq value's integer into `(bits[1..] packed into Fp, bit 0)` —
    /// the Type2 pair / kimchi `absorb_fr` split (`s_div_2 < 2^254` fits Fp).
    fn split_fq(t: Fq) -> (Fp, bool) {
        let bits = t.into_bigint().to_bits_le();
        let mut half = Fp::zero();
        for &b in bits[1..].iter().rev() {
            half.double_in_place();
            if b {
                half += Fp::one();
            }
        }
        (half, bits[0])
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
            let t1 = ShiftedScalar::Type1;
            let openings = OpeningProof {
                lr,
                delta: mkpt(sys, self.delta)?,
                z1: t1(mksc(sys, self.z1)?),
                z2: t1(mksc(sys, self.z2)?),
                challenge_polynomial_commitment: mkpt(sys, self.cpc)?,
                h_generator: mkpt(sys, self.h)?,
            };
            let advice = Advice {
                combined_inner_product: t1(mksc(sys, self.cip)?),
                b: t1(mksc(sys, self.b)?),
                perm: t1(mksc(sys, self.perm)?),
                zeta_to_srs_length: t1(mksc(sys, self.zeta_to_srs_length)?),
                zeta_to_domain_size: t1(mksc(sys, self.zeta_to_domain_size)?),
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
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        let (beta, gamma) = *out.clone();
        assert_eq!(beta, beta_ref, "beta (sponge order incl. sg_old)");
        assert_eq!(gamma, gamma_ref, "gamma");
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }

    // ---- the decisive test: equal_g == true against a real kimchi proof ----
    //
    // kimchi's berkeley linearization has zero index_terms
    // (kimchi/src/linearization.rs asserts it), so its f_comm carries only the
    // permutation term — the same split as pickles' Common.ft_comm. A plain
    // kimchi Pallas proof therefore satisfies the full pickles Fq-side
    // verifier, advice included.

    type PallasBase = DefaultFqSponge<
        mina_curves::pasta::PallasParameters,
        PlonkSpongeConstantsKimchi,
        { snarky::FULL_ROUNDS },
    >;
    type PallasScalar = DefaultFrSponge<Fq, PlonkSpongeConstantsKimchi, { snarky::FULL_ROUNDS }>;

    struct PallasAppCircuit {}
    impl SnarkyCircuit for PallasAppCircuit {
        type Curve = Pallas;
        type Proof = IpaProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = Fq;
        type PublicInput = FieldVar<Fq>;
        type PublicOutput = ();
        fn circuit(
            &self,
            sys: &mut RunState<Fq>,
            z: Self::PublicInput,
            private: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<()> {
            let x: FieldVar<Fq> = sys.compute(loc!(), |_| *private.unwrap())?;
            let xx = x.mul(&x, None, loc!(), sys)?;
            xx.assert_equals(sys, loc!(), &z)?;
            let _ = sys.poseidon(loc!(), (x, z));
            Ok(())
        }
    }

    /// Like `IvpCircuit`, but the deferred scalars are full-width field values
    /// (Type1 representatives of real Fq values, embedded into Fp) and the
    /// bulletproof-success boolean is exposed.
    struct RealIvpCircuit {
        vk_digest: Fp,
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
        xi: Fp,
        // Type2 split pairs (s_div_2, s_odd) of the Fq advice scalars
        cip: (Fp, bool),
        b: (Fp, bool),
        z1: (Fp, bool),
        z2: (Fp, bool),
        perm: (Fp, bool),
        zeta_to_srs_length: (Fp, bool),
        zeta_to_domain_size: (Fp, bool),
    }

    impl SnarkyCircuit for RealIvpCircuit {
        type Curve = Vesta;
        type Proof = IpaProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        /// (success, first raw IPA prechallenge — for transcript diagnosis)
        type PublicOutput = (Boolean<Fp>, FieldVar<Fp>);
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
            let w1 = |sys: &mut RunState<Fp>, v: Fp| sys.compute(loc!(), move |_| v);

            let vk_digest = w1(sys, self.vk_digest)?;
            let x_hat = mkpts(sys, &self.x_hat)?;
            let mut w_comm = vec![];
            for w in &self.w_comm {
                w_comm.push(mkpts(sys, w)?);
            }
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
                z_comm: mkpts(sys, &self.z_comm)?,
                t_comm: mkpts(sys, &self.t_comm)?,
            };
            let mut lr = vec![];
            for &(l, r) in &self.lr {
                lr.push((mkpt(sys, l)?, mkpt(sys, r)?));
            }
            let t2 = |sys: &mut RunState<Fp>,
                          p: (Fp, bool)|
             -> SnarkyResult<ShiftedScalar<Fp>> {
                let half = sys.compute(loc!(), move |_| p.0)?;
                let odd: Boolean<Fp> = sys.compute(loc!(), move |_| p.1)?;
                Ok(ShiftedScalar::Type2(half, odd))
            };
            let openings = OpeningProof {
                lr,
                delta: mkpt(sys, self.delta)?,
                z1: t2(sys, self.z1)?,
                z2: t2(sys, self.z2)?,
                challenge_polynomial_commitment: mkpt(sys, self.cpc)?,
                h_generator: mkpt(sys, self.h)?,
            };
            let advice = Advice {
                combined_inner_product: t2(sys, self.cip)?,
                b: t2(sys, self.b)?,
                perm: t2(sys, self.perm)?,
                zeta_to_srs_length: t2(sys, self.zeta_to_srs_length)?,
                zeta_to_domain_size: t2(sys, self.zeta_to_domain_size)?,
            };
            let xi = w1(sys, self.xi)?;

            use groupmap::GroupMap;
            let params = groupmap::BWParameters::<PallasParameters>::setup();
            let res = incrementally_verify_proof::<Fp, PallasParameters>(
                sys,
                loc!(),
                &vk_digest,
                &vk,
                &[],
                &x_hat,
                &messages,
                &openings,
                &advice,
                &xi,
                &params,
                crate::endo::tick::base(),
                <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1,
                NUM_BITS,
            )?;
            let success = Boolean::create_unsafe(res.success.to_field_var().seal(sys, loc!())?);
            let pre0 = res.bulletproof_challenges[0].clone().seal(sys, loc!())?;
            Ok((success, pre0))
        }
    }

    /// The full in-circuit `incrementally_verify_proof` ACCEPTS a real kimchi
    /// Pallas proof: `equal_g == true` with the genuine SRS, commitments,
    /// opening proof and Type1 advice — validating the whole Fq-side verifier
    /// (oracles, ft_comm, polyscale combination, IPA transcript and equation)
    /// against real data.
    #[test]
    fn incrementally_verify_proof_accepts_real_kimchi_proof() {
        use ark_ff::Field;
        use kimchi::circuits::wires::PERMUTS;
        use mina_curves::pasta::PallasParameters;
        use poly_commitment::commitment::{b_poly, shift_scalar, PolyComm};
        use poly_commitment::SRS;

        // 1. a real Pallas proof
        let (mut ppi, pver) = PallasAppCircuit {}.compile_to_indexes().unwrap();
        let vi = &pver.index;
        let x = Fq::from(3u64);
        let z = x * x;
        let (proof, _) = ppi.prove::<PallasBase, PallasScalar>(z, x, true).unwrap();

        // 2. kimchi's own oracles + the public commitment (our x_hat)
        let public_input = vec![z];
        let lgr = vi.srs().get_lagrange_basis(vi.domain);
        let com: Vec<_> = lgr.iter().take(vi.public).collect();
        let elm: Vec<_> = public_input.iter().map(|s| -*s).collect();
        let pc = PolyComm::<Pallas>::multi_scalar_mul(&com, &elm);
        let public_comm = vi
            .srs()
            .mask_custom(pc.clone(), &pc.map(|_| Fq::one()))
            .unwrap()
            .commitment;
        let o = proof
            .oracles::<PallasBase, PallasScalar, _>(vi, &public_comm, Some(&public_input))
            .unwrap();
        let oracles = &o.oracles;
        let (_, endo_q) = <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();

        // 3. the real IPA challenges, continuing kimchi's forked fq-sponge
        let (b_value, u_pt, ipa_chals, c_value) = {
            let mut sponge = o.fq_sponge.clone();
            sponge.absorb_fr(&[shift_scalar::<Pallas>(o.combined_inner_product)]);
            use groupmap::GroupMap;
            let gm = groupmap::BWParameters::<PallasParameters>::setup();
            use mina_poseidon::FqSponge as _;
            let t = sponge.challenge_fq();
            let u = gm.to_group(t);
            let chals = proof.proof.challenges::<PallasBase>(endo_q, &mut sponge);
            sponge.absorb_g(&[proof.proof.delta]);
            let c = mina_poseidon::sponge::ScalarChallenge::new(sponge.challenge())
                .to_field(endo_q);
            let zetaw = oracles.zeta * vi.domain.group_gen;
            let b = b_poly(&chals.chal, oracles.zeta) + oracles.u * b_poly(&chals.chal, zetaw);
            (b, u, chals, c)
        };

        // 4. the deferred plonk scalars (perm via our validated port)
        let combined = proof.evals.combine(&o.powers_of_eval_points_for_chunks);
        let srs_log2 = u64::BITS - 1 - (vi.max_poly_size as u64).leading_zeros();
        let domain = crate::plonk_checks::Domain::<Fq> {
            log2_size: vi.domain.log_size_of_group,
            generator: vi.domain.group_gen,
        };
        let minimal = crate::composition_types::plonk::Minimal::<Fq, Fq, bool> {
            alpha: oracles.alpha,
            beta: oracles.beta,
            gamma: oracles.gamma,
            zeta: oracles.zeta,
            joint_combiner: None,
            feature_flags: crate::composition_types::Features::none(),
        };
        let env = crate::plonk_checks::scalars_env::<Fq, bool>(&domain, srs_log2, &minimal);
        let evals = crate::plonk_checks::Evals {
            w: combined.w.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
            s: combined.s.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
            z: (combined.z.zeta, combined.z.zeta_omega),
        };
        let perm = crate::plonk_checks::perm_scalar(&env, &evals);
        let zeta_to_srs_length = oracles.zeta.pow([vi.max_poly_size as u64]);
        let zeta_to_domain_size = oracles.zeta.pow([vi.domain.size]);

        // -- diagnostic: our perm scalar vs kimchi's perm_scalars --
        {
            use ark_poly::Polynomial;
            use kimchi::circuits::argument::ArgumentType;
            use kimchi::circuits::constraints::ConstraintSystem;
            let pvp = vi
                .permutation_vanishing_polynomial_m()
                .evaluate(&oracles.zeta);
            let alphas = o
                .all_alphas
                .get_alphas(ArgumentType::Permutation, kimchi::circuits::polynomials::permutation::CONSTRAINTS);
            let kimchi_perm =
                ConstraintSystem::<Fq>::perm_scalars(&combined, oracles.beta, oracles.gamma, alphas, pvp);
            assert_eq!(perm, kimchi_perm, "perm scalar vs kimchi perm_scalars");
        }
        // -- diagnostic: our ft point vs kimchi's ft_comm, out of circuit --
        {
            use ark_ec::CurveGroup;
            let sigma_last = vi.sigma_comm[kimchi::circuits::wires::PERMUTS - 1].chunks[0];
            let mut t_red = proof.commitments.t_comm.chunks[6].into_group();
            for c in proof.commitments.t_comm.chunks[..6].iter().rev() {
                t_red = c.into_group() + t_red * zeta_to_srs_length;
            }
            let our_ft =
                (sigma_last * perm + t_red - t_red * zeta_to_domain_size).into_affine();
            let kimchi_ft = {
                let f = poly_commitment::commitment::PolyComm::multi_scalar_mul(
                    &[&vi.sigma_comm[kimchi::circuits::wires::PERMUTS - 1]],
                    &[perm],
                );
                let chunked_f = f.chunk_commitment(zeta_to_srs_length);
                let chunked_t = proof.commitments.t_comm.chunk_commitment(zeta_to_srs_length);
                (&chunked_f - &chunked_t.scale(zeta_to_domain_size - Fq::one())).chunks[0]
            };
            assert_eq!(our_ft, kimchi_ft, "ft_comm out-of-circuit");
        }

        // 5. the raw 128-bit polyscale challenge (v_chal) via Fr-sponge replay
        let claimed_xi = {
            use kimchi::plonk_sponge::FrSponge as _;
            let params = Pallas::sponge_params();
            let mut fr = PallasScalar::from(params);
            fr.absorb(&o.digest);
            let pcd = PallasScalar::from(params).digest();
            fr.absorb(&pcd);
            fr.absorb(&proof.ft_eval1);
            fr.absorb_multiple(&o.public_evals[0]);
            fr.absorb_multiple(&o.public_evals[1]);
            fr.absorb_evaluations(&proof.evals);
            fr.squeeze(mina_poseidon::sponge::CHALLENGE_LENGTH_IN_LIMBS)
        };

        // -- diagnostic: xi replay and the full equation, out of circuit --
        {
            use ark_ec::CurveGroup;
            use kimchi::circuits::wires::PERMUTS;
            // xi replay: to_field(v_chal) == oracles.v
            assert_eq!(
                mina_poseidon::sponge::ScalarChallenge::new(claimed_xi).to_field(endo_q),
                oracles.v,
                "xi replay"
            );
            // the pickles-side combined commitment
            let sigma_last = vi.sigma_comm[PERMUTS - 1].chunks[0];
            let mut t_red = proof.commitments.t_comm.chunks[6].into_group();
            for ch in proof.commitments.t_comm.chunks[..6].iter().rev() {
                t_red = ch.into_group() + t_red * zeta_to_srs_length;
            }
            let ft = sigma_last * perm + t_red - t_red * zeta_to_domain_size;
            let mut comms: Vec<<Pallas as AffineRepr>::Group> = vec![
                public_comm.chunks[0].into_group(),
                ft,
                proof.commitments.z_comm.chunks[0].into_group(),
                vi.generic_comm.chunks[0].into_group(),
                vi.psm_comm.chunks[0].into_group(),
                vi.complete_add_comm.chunks[0].into_group(),
                vi.mul_comm.chunks[0].into_group(),
                vi.emul_comm.chunks[0].into_group(),
                vi.endomul_scalar_comm.chunks[0].into_group(),
            ];
            comms.extend(
                proof
                    .commitments
                    .w_comm
                    .iter()
                    .map(|c| c.chunks[0].into_group()),
            );
            comms.extend(vi.coefficients_comm.iter().map(|c| c.chunks[0].into_group()));
            comms.extend(
                vi.sigma_comm[..PERMUTS - 1]
                    .iter()
                    .map(|c| c.chunks[0].into_group()),
            );
            let mut combined_pt = *comms.last().unwrap();
            for cpt in comms[..comms.len() - 1].iter().rev() {
                combined_pt = *cpt + combined_pt * oracles.v;
            }
            // lr_prod
            let mut lr_prod = Pallas::zero().into_group();
            for ((l, r), (ci, c)) in proof
                .proof
                .lr
                .iter()
                .zip(ipa_chals.chal_inv.iter().zip(&ipa_chals.chal))
            {
                lr_prod += *l * *ci + *r * *c;
            }
            let u_base = Pallas::new_unchecked(u_pt.0, u_pt.1);
            let q = combined_pt + u_base * o.combined_inner_product + lr_prod;
            let lhs = q * c_value + proof.proof.delta.into_group();
            let rhs = (proof.proof.sg.into_group() + u_base * b_value) * proof.proof.z1
                + vi.srs().h.into_group() * proof.proof.z2;
            assert_eq!(
                lhs.into_affine(),
                rhs.into_affine(),
                "IPA equation out-of-circuit"
            );
        }

        // -- diagnostic: full ArithmeticSponge<Fp> replay of the transcript,
        //    bisecting where the in-circuit continuation would diverge --
        {
            use mina_poseidon::FqSponge as _;
            let mut s = RefSponge::new(Vesta::sponge_params());
            let abpt = |s: &mut RefSponge, p: &Pallas| {
                s.absorb(&[p.x]);
                s.absorb(&[p.y]);
            };
            s.absorb(&[vi.digest::<PallasBase>()]);
            abpt(&mut s, &public_comm.chunks[0]);
            for w in &proof.commitments.w_comm {
                abpt(&mut s, &w.chunks[0]);
            }
            let beta_r = s.squeeze();
            let gamma_r = s.squeeze();
            let l128 = |x: Fp| {
                let mut acc = 0u128;
                for &b in x.into_bigint().to_bits_le()[..128].iter().rev() {
                    acc = (acc << 1) | u128::from(b);
                }
                acc
            };
            let l128q = |x: Fq| {
                let mut acc = 0u128;
                for &b in x.into_bigint().to_bits_le()[..128].iter().rev() {
                    acc = (acc << 1) | u128::from(b);
                }
                acc
            };
            assert_eq!(l128(beta_r), l128q(oracles.beta), "replay beta");
            assert_eq!(l128(gamma_r), l128q(oracles.gamma), "replay gamma");
            abpt(&mut s, &proof.commitments.z_comm.chunks[0]);
            let alpha_r = s.squeeze();
            assert_eq!(
                mina_poseidon::sponge::ScalarChallenge::new(Fq::from_le_bytes_mod_order(
                    &Fp::from(l128(alpha_r)).into_bigint().to_bytes_le()
                ))
                .to_field(endo_q),
                oracles.alpha,
                "replay alpha"
            );
            for t in &proof.commitments.t_comm.chunks {
                abpt(&mut s, t);
            }
            let zeta_r = s.squeeze();
            assert_eq!(
                mina_poseidon::sponge::ScalarChallenge::new(Fq::from(l128q(Fq::from(
                    l128(zeta_r)
                ))))
                .to_field(endo_q),
                oracles.zeta,
                "replay zeta"
            );
            // fork: continue the IPA transcript exactly as the circuit does.
            // Fq > Fp, so kimchi's shift_scalar is the Type2 shift (x - 2^255)
            // and absorb_fr splits it into (s_div_2, s_odd) — two elements.
            let repr = crate::shifted_value::type2_of_field(o.combined_inner_product);
            assert_eq!(
                repr,
                shift_scalar::<Pallas>(o.combined_inner_product),
                "type2_of_field vs kimchi shift_scalar"
            );
            let (half, odd) = split_fq(repr);
            s.absorb(&[half]);
            s.absorb(&[if odd { Fp::one() } else { Fp::zero() }]);
            let t_ours = s.squeeze();
            // kimchi's t
            let t_kimchi = {
                let mut sp = o.fq_sponge.clone();
                sp.absorb_fr(&[shift_scalar::<Pallas>(o.combined_inner_product)]);
                sp.challenge_fq()
            };
            assert_eq!(t_ours, t_kimchi, "group-map input t (post-cip squeeze)");
        }

        // 6. Type2 split representatives of the Fq advice: the pair
        //    (s_div_2, s_odd) of t = value - 2^255 mod q (s_div_2 < 2^254 fits Fp)
        let t2 = |s: Fq| split_fq(crate::shifted_value::type2_of_field(s));
        // the raw 128-bit xi fits either field directly
        let emb = |s: Fq| Fp::from_le_bytes_mod_order(&s.into_bigint().to_bytes_le());

        let coords = |c: &PolyComm<Pallas>| -> Vec<(Fp, Fp)> {
            c.chunks.iter().map(|p| (p.x, p.y)).collect()
        };
        let pt = |p: &Pallas| (p.x, p.y);
        let srs_h = vi.srs().h;

        let circ = RealIvpCircuit {
            vk_digest: vi.digest::<PallasBase>(),
            x_hat: coords(&public_comm),
            w_comm: proof.commitments.w_comm.iter().map(coords).collect(),
            z_comm: coords(&proof.commitments.z_comm),
            t_comm: coords(&proof.commitments.t_comm),
            generic: pt(&vi.generic_comm.chunks[0]),
            psm: pt(&vi.psm_comm.chunks[0]),
            complete_add: pt(&vi.complete_add_comm.chunks[0]),
            mul: pt(&vi.mul_comm.chunks[0]),
            emul: pt(&vi.emul_comm.chunks[0]),
            endomul_scalar: pt(&vi.endomul_scalar_comm.chunks[0]),
            coefficients: vi
                .coefficients_comm
                .iter()
                .map(|c| pt(&c.chunks[0]))
                .collect(),
            sigma_init: vi.sigma_comm[..PERMUTS - 1]
                .iter()
                .map(|c| pt(&c.chunks[0]))
                .collect(),
            sigma_last: vec![pt(&vi.sigma_comm[PERMUTS - 1].chunks[0])],
            lr: proof
                .proof
                .lr
                .iter()
                .map(|(l, r)| (pt(l), pt(r)))
                .collect(),
            delta: pt(&proof.proof.delta),
            cpc: pt(&proof.proof.sg),
            h: (srs_h.x, srs_h.y),
            xi: emb(claimed_xi),
            cip: t2(o.combined_inner_product),
            b: t2(b_value),
            z1: t2(proof.proof.z1),
            z2: t2(proof.proof.z2),
            perm: t2(perm),
            zeta_to_srs_length: t2(zeta_to_srs_length),
            zeta_to_domain_size: t2(zeta_to_domain_size),
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (cproof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        let (success, pre0) = *out.clone();
        // transcript diagnosis: the endo image of the first in-circuit raw
        // prechallenge must equal kimchi's field-form challenge
        let pre0_fq = Fq::from_le_bytes_mod_order(&pre0.into_bigint().to_bytes_le());
        assert_eq!(
            mina_poseidon::sponge::ScalarChallenge::new(pre0_fq).to_field(endo_q),
            ipa_chals.chal[0],
            "in-circuit prechallenge 0 vs kimchi"
        );
        assert!(success, "equal_g must hold on a real kimchi proof");
        ver.verify::<BaseSponge, ScalarSponge>(cproof, (), *out);
    }
}
