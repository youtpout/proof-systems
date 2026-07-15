//! Prover-side witness computation for the wrap circuit (the heart of
//! `wrap.ml::deferred_values_and_hints`): given a *step* (Vesta) proof, its
//! verifier index and public input, recompute everything `wrap_main` witnesses
//! — the raw Fiat-Shamir challenges (by replaying the fq-sponge transcript,
//! since kimchi keeps the raw scalar challenges private), the IPA transcript
//! values, and the `Shifted_value.Type1` deferred scalars (Tick values fit the
//! Tock circuit field, so single representatives).
//!
//! [`crate::wrap_deferred_values::expand_deferred`] covers the finalize half
//! (cip/b/perm as stored in the statement); this adds the transcript half.

use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use kimchi::{curve::KimchiCurve, proof::ProverProof};
use mina_curves::pasta::{Fp, Fq, Vesta};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi,
    poseidon::{ArithmeticSponge, Sponge as _},
};
use poly_commitment::ipa::OpeningProof;

use crate::common::FULL_ROUNDS;

type FqSpongeRef = ArithmeticSponge<Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

/// The transcript witness of one step (Vesta) proof, as the wrap circuit
/// re-derives it. Raw challenges are 128-bit values in Fq (the wrap circuit
/// field); the deferred scalars are Tick (Fp) values whose `Type1`
/// representatives are given directly (they fit in Fq).
pub struct WrapWitness {
    // raw 128-bit oracle challenges (squeezed from the Fq transcript sponge)
    pub beta_raw: Fq,
    pub gamma_raw: Fq,
    pub alpha_raw: Fq,
    pub zeta_raw: Fq,
    /// `sponge_digest_before_evaluations` (converted to the scalar field
    /// exactly as kimchi's `FqSponge::digest`).
    pub sponge_digest: Fp,
    /// The step proof's IPA round prechallenges (raw 128-bit).
    pub bulletproof_prechallenges: Vec<Fq>,
    // Type1 representatives (Fp) of the deferred scalars fed to the IVP advice
    pub cip_repr: Fp,
    pub b_repr: Fp,
    pub perm_repr: Fp,
    pub zeta_to_srs_length_repr: Fp,
    pub zeta_to_domain_size_repr: Fp,
    pub z1_repr: Fp,
    pub z2_repr: Fp,
}

/// The low 128 bits of an Fq element (a squeezed challenge).
fn low_128(x: Fq) -> Fq {
    let bits = x.into_bigint().to_bits_le();
    let mut acc = Fq::zero();
    for &b in bits[..128].iter().rev() {
        acc = acc + acc;
        if b {
            acc += Fq::one();
        }
    }
    acc
}

/// Replays the whole Fq-sponge transcript of a Vesta proof and derives the
/// wrap-circuit witness. `public_comm` is the (blinded) public-input
/// commitment; `oracles`/`combined_inner_product` come from kimchi's
/// `proof.oracles()` (used for the field-image scalars the replay cannot
/// recover more cheaply).
///
/// The b value is `h(ζ) + r·h(ζω)` over the *field-form* IPA challenges,
/// obtained by continuing the replayed sponge through the opening proof.
#[allow(clippy::too_many_arguments)]
pub fn wrap_witness(
    max_poly_size: u64,
    domain_size: u64,
    domain_gen: Fp,
    proof: &ProverProof<Vesta, OpeningProof<Vesta, FULL_ROUNDS>, FULL_ROUNDS>,
    public_comm: &poly_commitment::commitment::PolyComm<Vesta>,
    vk_digest: Fq,
    sg_olds: &[Vesta],
    sg_old_mask: Option<&[bool]>,
    combined_inner_product: Fp,
    zeta: Fp,
    evalscale: Fp,
    perm: Fp,
) -> WrapWitness {
    use poly_commitment::commitment::b_poly;

    let params = <Vesta as KimchiCurve<FULL_ROUNDS>>::other_curve_sponge_params();
    let mut s = FqSpongeRef::new(params);
    let abpt = |s: &mut FqSpongeRef, p: &Vesta| {
        s.absorb(&[p.x]);
        s.absorb(&[p.y]);
    };
    let default_sg_old_mask;
    let sg_old_mask = if let Some(mask) = sg_old_mask {
        assert_eq!(mask.len(), sg_olds.len(), "one mask bit per sg_old");
        mask
    } else {
        default_sg_old_mask = vec![true; sg_olds.len()];
        &default_sg_old_mask
    };

    // oracle transcript: vk digest, then the accumulated challenge-polynomial
    // commitments (kimchi absorbs the recursion challenges' commitments right
    // after the index digest), then the public commitment and the messages
    s.absorb(&[vk_digest]);
    for (keep, sg) in sg_old_mask.iter().zip(sg_olds) {
        if *keep {
            abpt(&mut s, sg);
        } else {
            s.absorb(&[Fq::zero()]);
            s.absorb(&[Fq::zero()]);
        }
    }
    for c in &public_comm.chunks {
        abpt(&mut s, c);
    }
    for w in &proof.commitments.w_comm {
        abpt(&mut s, &w.chunks[0]);
    }
    let beta_raw = low_128(s.squeeze());
    let gamma_raw = low_128(s.squeeze());
    abpt(&mut s, &proof.commitments.z_comm.chunks[0]);
    let alpha_raw = low_128(s.squeeze());
    for t in &proof.commitments.t_comm.chunks {
        abpt(&mut s, t);
    }
    let zeta_raw = low_128(s.squeeze());

    // fork: digest on a clone, IPA transcript on the original.
    // kimchi's digest() converts the base-field squeeze to the scalar field,
    // returning zero for out-of-range values (sponge.rs::digest).
    let sponge_digest = {
        let d: Fq = s.clone().squeeze();
        Fp::from_bigint(<Fp as PrimeField>::BigInt::from_bits_le(
            &d.into_bigint().to_bits_le(),
        ))
        .unwrap_or_else(Fp::zero)
    };

    // Type1 representatives of the deferred scalars
    let t1 = crate::shifted_value::type1_of_field::<Fp>;
    let cip_repr = t1(combined_inner_product);
    let zeta_to_srs_length = zeta.pow([max_poly_size]);
    let zeta_to_domain_size = zeta.pow([domain_size]);

    // IPA transcript: absorb the Type1 repr (Fp < Fq: a single element),
    // squeeze the group-map input, then the round prechallenges and c
    let repr_fq = Fq::from_le_bytes_mod_order(&cip_repr.into_bigint().to_bytes_le());
    s.absorb(&[repr_fq]);
    let _t_groupmap = s.squeeze();
    let mut prechallenges = Vec::with_capacity(proof.proof.lr.len());
    for (l, r) in &proof.proof.lr {
        abpt(&mut s, l);
        abpt(&mut s, r);
        prechallenges.push(low_128(s.squeeze()));
    }
    abpt(&mut s, &proof.proof.delta);
    let _c_raw = low_128(s.squeeze());

    // b = h(ζ) + r·h(ζω) over the field-form challenges
    let endo_p = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1;
    let chals: Vec<Fp> = prechallenges
        .iter()
        .map(|&raw| {
            let raw_fp = Fp::from_le_bytes_mod_order(&raw.into_bigint().to_bytes_le());
            crate::scalar_challenge::ScalarChallenge(raw_fp).to_field(endo_p)
        })
        .collect();
    let zetaw = zeta * domain_gen;
    let b_value = b_poly(&chals, zeta) + evalscale * b_poly(&chals, zetaw);

    WrapWitness {
        beta_raw,
        gamma_raw,
        alpha_raw,
        zeta_raw,
        sponge_digest,
        bulletproof_prechallenges: prechallenges,
        cip_repr,
        b_repr: t1(b_value),
        perm_repr: t1(perm),
        zeta_to_srs_length_repr: t1(zeta_to_srs_length),
        zeta_to_domain_size_repr: t1(zeta_to_domain_size),
        z1_repr: t1(proof.proof.z1),
        z2_repr: t1(proof.proof.z2),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::One;
    use mina_curves::pasta::VestaParameters;
    use mina_poseidon::sponge::{DefaultFqSponge, DefaultFrSponge};
    use poly_commitment::{
        commitment::{shift_scalar, PolyComm},
        SRS,
    };
    use snarky::{api::SnarkyCircuit, loc, FieldVar, RunState, SnarkyResult};

    type BaseSponge = DefaultFqSponge<VestaParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
    type ScalarSponge = DefaultFrSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

    struct SmallCircuit {}
    impl SnarkyCircuit for SmallCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, FULL_ROUNDS>;
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

    /// The replayed transcript witness matches kimchi's own oracles on a real
    /// Vesta proof: raw challenges map to the oracle field images through the
    /// endomorphism, the digest matches, the Type1 cip representative equals
    /// kimchi's shift_scalar, and b's prechallenges continue the same sponge.
    #[test]
    fn wrap_witness_matches_kimchi_oracles() {
        let circuit = SmallCircuit {};
        let (mut pi, ver) = circuit.compile_to_indexes().unwrap();
        let vi = &ver.index;
        let x = Fp::from(5u64);
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

        // perm via our (kimchi-parity-tested) port
        let combined = proof.evals.combine(&o.powers_of_eval_points_for_chunks);
        let srs_log2 = u64::BITS - 1 - (vi.max_poly_size as u64).leading_zeros();
        let domain = crate::plonk_checks::Domain::<Fp> {
            log2_size: vi.domain.log_size_of_group,
            generator: vi.domain.group_gen,
        };
        let minimal = crate::composition_types::plonk::Minimal::<Fp, Fp, bool> {
            alpha: oracles.alpha,
            beta: oracles.beta,
            gamma: oracles.gamma,
            zeta: oracles.zeta,
            joint_combiner: None,
            feature_flags: crate::composition_types::Features::none(),
        };
        let env = crate::plonk_checks::scalars_env::<Fp, bool>(&domain, srs_log2, &minimal);
        let evals = crate::plonk_checks::Evals {
            w: combined.w.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
            s: combined.s.iter().map(|p| (p.zeta, p.zeta_omega)).collect(),
            z: (combined.z.zeta, combined.z.zeta_omega),
        };
        let perm = crate::plonk_checks::perm_scalar(&env, &evals);

        let w = wrap_witness(
            vi.max_poly_size as u64,
            vi.domain.size,
            vi.domain.group_gen,
            &proof,
            &public_comm,
            vi.digest::<BaseSponge>(),
            &[],
            None,
            o.combined_inner_product,
            oracles.zeta,
            oracles.u,
            perm,
        );

        let endo_p = <Vesta as KimchiCurve<FULL_ROUNDS>>::endos().1;
        let to_fp = |x: Fq| Fp::from_le_bytes_mod_order(&x.into_bigint().to_bytes_le());
        // raw challenges: beta/gamma are used raw by kimchi; alpha/zeta map
        // through the endomorphism
        assert_eq!(to_fp(w.beta_raw), oracles.beta, "beta");
        assert_eq!(to_fp(w.gamma_raw), oracles.gamma, "gamma");
        assert_eq!(
            crate::scalar_challenge::ScalarChallenge(to_fp(w.alpha_raw)).to_field(endo_p),
            oracles.alpha,
            "alpha raw -> field"
        );
        assert_eq!(
            crate::scalar_challenge::ScalarChallenge(to_fp(w.zeta_raw)).to_field(endo_p),
            oracles.zeta,
            "zeta raw -> field"
        );
        // digest
        assert_eq!(w.sponge_digest, o.digest, "sponge digest");
        // Type1 cip representative == kimchi's shift_scalar (Fp < Fq branch)
        assert_eq!(
            w.cip_repr,
            shift_scalar::<Vesta>(o.combined_inner_product),
            "cip repr"
        );
        // the prechallenges continue kimchi's own forked sponge
        let kimchi_chals = {
            use mina_poseidon::FqSponge as _;
            let mut sp = o.fq_sponge.clone();
            sp.absorb_fr(&[shift_scalar::<Vesta>(o.combined_inner_product)]);
            let _t = sp.challenge_fq();
            proof.proof.challenges::<BaseSponge>(&endo_p, &mut sp).chal
        };
        let our_chals: Vec<Fp> = w
            .bulletproof_prechallenges
            .iter()
            .map(|&raw| crate::scalar_challenge::ScalarChallenge(to_fp(raw)).to_field(endo_p))
            .collect();
        assert_eq!(our_chals, kimchi_chals, "IPA challenges");
        // b_repr round-trips to h(zeta) + r*h(zetaw)
        use poly_commitment::commitment::b_poly;
        let zetaw = oracles.zeta * vi.domain.group_gen;
        let b_ref = b_poly(&kimchi_chals, oracles.zeta) + oracles.u * b_poly(&kimchi_chals, zetaw);
        assert_eq!(
            crate::shifted_value::type1_to_field(w.b_repr),
            b_ref,
            "b repr"
        );
    }
}
