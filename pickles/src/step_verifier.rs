//! Assembly of `Step_verifier.verify` (`step_verifier.ml`, lines ~1244–1317):
//! full verification of one wrap proof inside a step circuit.
//!
//! ```text
//! x_hat   = public_input_commitment(packed wrap statement)   // IVC steps 3-4
//! result  = incrementally_verify_proof(...)                  // oracles + IPA
//! assert  result.sponge_digest == unfinalized.sponge_digest  // step 4a
//! assert  result.bulletproof_challenges == claimed           // step 4b
//!         (base case: bypassed — claimed compared to itself)
//! assert  result.oracles == statement plonk challenges       // assert_eq_plonk
//! return  result.success
//! ```
//!
//! The wrap statement arrives already packed as public-input [`Term`]s (the
//! caller flattens it in the `Wrap.Statement.to_data` order with the right bit
//! widths and attaches the Lagrange constants); the claimed plonk challenges
//! are the *raw* 128-bit scalar challenges from the statement.

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{gadgets::curve::Point, Boolean, FieldVar, RunState, SnarkyResult};

use crate::incrementally_verify::{
    incrementally_verify_proof, Advice, IncrementalResult, Messages, OpeningProof,
    VerificationKeyComm,
};
use crate::public_input::{public_input_commitment, Term};

/// The claimed values `verify` checks the re-derived transcript against: the
/// statement's raw 128-bit plonk challenges, the sponge digest, and the
/// bulletproof prechallenges of the unfinalized proof.
pub struct Claimed<F: PrimeField> {
    pub beta: FieldVar<F>,
    pub gamma: FieldVar<F>,
    pub alpha: FieldVar<F>,
    pub zeta: FieldVar<F>,
    pub sponge_digest_before_evaluations: FieldVar<F>,
    pub bulletproof_challenges: Vec<FieldVar<F>>,
}

/// Full verification of one wrap proof (`Step_verifier.verify`). Returns the
/// bulletproof success boolean; everything else is asserted.
///
/// `is_base_case` bypasses the bulletproof-challenge comparison (a base-case
/// proof carries dummy challenges with no transcript to match). The digest and
/// plonk-challenge asserts are unconditional, as in OCaml.
#[allow(clippy::too_many_arguments)]
pub fn verify<F, C>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    vk_digest: &FieldVar<F>,
    vk: &VerificationKeyComm<F>,
    sg_old: &[Point<F>],
    public_input_terms: &[Term<F>],
    h_generator: &Point<F>,
    messages: &Messages<F>,
    openings: &OpeningProof<F>,
    advice: &Advice<F>,
    xi: &FieldVar<F>,
    claimed: &Claimed<F>,
    is_base_case: &Boolean<F>,
    group_map_params: &groupmap::BWParameters<C>,
    endo_base: F,
    endo_scalar: <ark_ec::short_weierstrass::Affine<C> as ark_ec::AffineRepr>::ScalarField,
    num_bits: usize,
) -> SnarkyResult<Boolean<F>>
where
    F: PrimeField,
    C: ark_ec::short_weierstrass::SWCurveConfig<BaseField = F>,
{
    // == IVC steps 3-4: commit to the packed statement ==
    let x_hat = public_input_commitment(sys, loc.clone(), public_input_terms, h_generator)?;

    // == oracles + IPA ==
    let IncrementalResult {
        success,
        oracles,
        sponge_digest,
        bulletproof_challenges,
    } = incrementally_verify_proof::<F, C>(
        sys,
        loc.clone(),
        vk_digest,
        vk,
        sg_old,
        std::slice::from_ref(&x_hat),
        messages,
        openings,
        advice,
        xi,
        group_map_params,
        endo_base,
        endo_scalar,
        num_bits,
    )?;

    // == step 4a: the sponge digest must match the claimed one ==
    sponge_digest.assert_equals(
        sys,
        loc.clone(),
        &claimed.sponge_digest_before_evaluations,
    )?;

    // == step 4b: bulletproof challenges must match (base case bypassed) ==
    assert_eq!(
        claimed.bulletproof_challenges.len(),
        bulletproof_challenges.len(),
        "verify: claimed/actual bulletproof challenge count"
    );
    for (c1, c2) in claimed
        .bulletproof_challenges
        .iter()
        .zip(&bulletproof_challenges)
    {
        // in the base case compare c1 with itself, else with the actual c2
        let rhs = sys.if_(loc.clone(), is_base_case.clone(), c1.clone(), c2.clone())?;
        c1.assert_equals(sys, loc.clone(), &rhs)?;
    }

    // == assert_eq_plonk: sampled raw challenges == statement's ==
    oracles.beta.assert_equals(sys, loc.clone(), &claimed.beta)?;
    oracles
        .gamma
        .assert_equals(sys, loc.clone(), &claimed.gamma)?;
    oracles
        .alpha
        .assert_equals(sys, loc.clone(), &claimed.alpha)?;
    oracles.zeta.assert_equals(sys, loc, &claimed.zeta)?;

    Ok(success)
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

    const NUM_BITS: usize = 255;

    /// End-to-end structural run of `verify` in a base-case setting: the
    /// claimed digest and plonk challenges are produced by an out-of-circuit
    /// mirror of the oracle transcript (so the asserts hold), the bulletproof
    /// challenge check is bypassed by `is_base_case = true`, and the statement
    /// is committed through the x_hat gadget from packed terms. The success
    /// boolean is exposed (not asserted — needs a real pickles statement).
    struct VerifyCircuit {
        vk_digest: Fp,
        sg_old: Vec<(Fp, Fp)>,
        // packed statement inputs: (value, num_bits) with 128/255-bit mix
        inputs: Vec<(Fp, usize)>,
        lagranges: Vec<(Fp, Fp)>,
        corrections: Vec<(Fp, Fp)>,
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
        claimed_beta: Fp,
        claimed_gamma: Fp,
        claimed_alpha: Fp,
        claimed_zeta: Fp,
        claimed_digest: Fp,
        claimed_bp: Vec<Fp>,
    }

    impl SnarkyCircuit for VerifyCircuit {
        type Curve = Vesta;
        type Proof = IpaProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        type PublicOutput = Boolean<Fp>;
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
            let cpt = |p: (Fp, Fp)| Point::new(FieldVar::constant(p.0), FieldVar::constant(p.1));

            let vk_digest: FieldVar<Fp> = sys.compute(loc!(), |_| self.vk_digest)?;
            let sg_old = mkpts(sys, &self.sg_old)?;

            // statement terms (all Packed in this test)
            let mut terms = vec![];
            for (i, &(v, n)) in self.inputs.iter().enumerate() {
                let value: FieldVar<Fp> = sys.compute(loc!(), move |_| v)?;
                terms.push(Term::Packed {
                    value,
                    num_bits: n,
                    lagrange: cpt(self.lagranges[i]),
                    correction: cpt(self.corrections[i]),
                });
            }

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
            let h = cpt(self.h);
            let openings = OpeningProof {
                lr,
                delta: mkpt(sys, self.delta)?,
                z1: mksc(sys, self.z1)?,
                z2: mksc(sys, self.z2)?,
                challenge_polynomial_commitment: mkpt(sys, self.cpc)?,
                h_generator: h.clone(),
            };
            let advice = Advice {
                combined_inner_product: mksc(sys, self.cip)?,
                b: mksc(sys, self.b)?,
                perm: mksc(sys, self.perm)?,
                zeta_to_srs_length: mksc(sys, self.zeta_to_srs_length)?,
                zeta_to_domain_size: mksc(sys, self.zeta_to_domain_size)?,
            };
            let xi = mksc(sys, self.xi)?;

            let mut claimed_bp = vec![];
            for &c in &self.claimed_bp {
                claimed_bp.push(sys.compute(loc!(), move |_| c)?);
            }
            let claimed = Claimed {
                beta: sys.compute(loc!(), |_| self.claimed_beta)?,
                gamma: sys.compute(loc!(), |_| self.claimed_gamma)?,
                alpha: sys.compute(loc!(), |_| self.claimed_alpha)?,
                zeta: sys.compute(loc!(), |_| self.claimed_zeta)?,
                sponge_digest_before_evaluations: sys.compute(loc!(), |_| self.claimed_digest)?,
                bulletproof_challenges: claimed_bp,
            };
            let is_base_case: Boolean<Fp> = sys.compute(loc!(), |_| true)?;

            use groupmap::GroupMap;
            let params = groupmap::BWParameters::<PallasParameters>::setup();
            let success = verify::<Fp, PallasParameters>(
                sys,
                loc!(),
                &vk_digest,
                &vk,
                &sg_old,
                &terms,
                &h,
                &messages,
                &openings,
                &advice,
                &xi,
                &claimed,
                &is_base_case,
                &params,
                crate::endo::tick::base(),
                <Pallas as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos().1,
                NUM_BITS,
            )?;
            let success = Boolean::create_unsafe(success.to_field_var().seal(sys, loc!())?);
            Ok(success)
        }
    }

    /// `verify` composes x_hat + IVP + asserts into one satisfiable circuit
    /// when the claimed digest/challenges come from a transcript mirror.
    #[test]
    fn verify_assembles_with_consistent_claims() {
        use groupmap::GroupMap;
        let mut rng = o1_utils::tests::make_test_rng(None);
        let rand_pt = |rng: &mut _| (Pallas::generator() * Fq::rand(rng)).into_affine();
        let pt = |rng: &mut _| {
            let p = rand_pt(rng);
            (p.x, p.y)
        };

        let vk_digest = Fp::rand(&mut rng);
        let sg_old_pts = [rand_pt(&mut rng)];
        // statement inputs: 2×128-bit + 1×255-bit
        let inputs: Vec<(Fp, usize)> = vec![
            (Fp::from(u128::rand(&mut rng)), 128),
            (Fp::from(u128::rand(&mut rng)), 128),
            (
                crate::shifted_value::embed_repr::<Fq, Fp>(Fq::rand(&mut rng)),
                255,
            ),
        ];
        let lagrange_pts: Vec<Pallas> = (0..3).map(|_| rand_pt(&mut rng)).collect();
        let corrections: Vec<Pallas> = lagrange_pts
            .iter()
            .zip(&inputs)
            .map(|(l, (_, n))| crate::public_input::lagrange_correction(l, *n))
            .collect();
        let h = rand_pt(&mut rng);

        let w_comm_pts: Vec<Pallas> = (0..15).map(|_| rand_pt(&mut rng)).collect();
        let z_comm_pt = rand_pt(&mut rng);
        let t_comm_pts: Vec<Pallas> = (0..7).map(|_| rand_pt(&mut rng)).collect();

        // out-of-circuit mirror: x_hat, then the oracle transcript
        let x_hat = {
            let mut sum = Pallas::zero().into_group();
            for ((v, _n), l) in inputs.iter().zip(&lagrange_pts) {
                // value · L  (recover the integer scalar from the Fp value)
                let scalar = Fq::from_le_bytes_mod_order(&v.into_bigint().to_bytes_le());
                sum += *l * scalar;
            }
            (-sum + h).into_affine()
        };
        let mut s = RefSponge::new(Vesta::sponge_params());
        let absorb_pt = |s: &mut RefSponge, p: &Pallas| {
            s.absorb(&[p.x]);
            s.absorb(&[p.y]);
        };
        s.absorb(&[vk_digest]);
        for sg in &sg_old_pts {
            absorb_pt(&mut s, sg);
        }
        absorb_pt(&mut s, &x_hat);
        for w in &w_comm_pts {
            absorb_pt(&mut s, w);
        }
        let claimed_beta = lowest_128(s.squeeze());
        let claimed_gamma = lowest_128(s.squeeze());
        absorb_pt(&mut s, &z_comm_pt);
        let claimed_alpha = lowest_128(s.squeeze());
        for t in &t_comm_pts {
            absorb_pt(&mut s, t);
        }
        let claimed_zeta = lowest_128(s.squeeze());
        let claimed_digest = s.squeeze();

        let params = groupmap::BWParameters::<PallasParameters>::setup();
        let _ = &params;

        let circ = VerifyCircuit {
            vk_digest,
            sg_old: sg_old_pts.iter().map(|p| (p.x, p.y)).collect(),
            inputs,
            lagranges: lagrange_pts.iter().map(|p| (p.x, p.y)).collect(),
            corrections: corrections.iter().map(|p| (p.x, p.y)).collect(),
            w_comm: w_comm_pts.iter().map(|p| vec![(p.x, p.y)]).collect(),
            z_comm: vec![(z_comm_pt.x, z_comm_pt.y)],
            t_comm: t_comm_pts.iter().map(|p| (p.x, p.y)).collect(),
            generic: pt(&mut rng),
            psm: pt(&mut rng),
            complete_add: pt(&mut rng),
            mul: pt(&mut rng),
            emul: pt(&mut rng),
            endomul_scalar: pt(&mut rng),
            coefficients: (0..15).map(|_| pt(&mut rng)).collect(),
            sigma_init: (0..6).map(|_| pt(&mut rng)).collect(),
            sigma_last: vec![pt(&mut rng)],
            lr: (0..2).map(|_| (pt(&mut rng), pt(&mut rng))).collect(),
            delta: pt(&mut rng),
            cpc: pt(&mut rng),
            h: (h.x, h.y),
            xi: u128::rand(&mut rng),
            cip: u128::rand(&mut rng),
            b: u128::rand(&mut rng),
            z1: u128::rand(&mut rng),
            z2: u128::rand(&mut rng),
            perm: u128::rand(&mut rng),
            zeta_to_srs_length: u128::rand(&mut rng),
            zeta_to_domain_size: u128::rand(&mut rng),
            claimed_beta,
            claimed_gamma,
            claimed_alpha,
            claimed_zeta,
            claimed_digest,
            // base case: compared against themselves
            claimed_bp: (0..2).map(|_| Fp::from(u128::rand(&mut rng))).collect(),
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        // success is not asserted true (random data cannot satisfy the IPA
        // equation) — the point is that every assert in `verify` held.
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }
}
