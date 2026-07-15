//! Prover-side witness computation for a *step* circuit verifying a wrap
//! (Pallas) proof — the mirror of [`crate::wrap::wrap_witness`] on the other
//! side of the cycle (the transcript half of `step.ml`'s per-proof witness).
//!
//! The wrap proof's transcript sponge runs over Fp; its deferred scalars live
//! in Fq, which does *not* fit the step circuit's field — they are carried as
//! `Shifted_value.Type2` split pairs (see
//! [`crate::plonk_curve_ops::ShiftedScalar::Type2`]), and the combined inner
//! product is absorbed as its two split limbs, exactly like kimchi's
//! `absorb_fr` in the `Fr > Fq` case.

use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use kimchi::{curve::KimchiCurve, proof::ProverProof};
use mina_curves::pasta::{Fp, Fq, Pallas};
use mina_poseidon::{
    constants::PlonkSpongeConstantsKimchi,
    poseidon::{ArithmeticSponge, Sponge as _},
};
use poly_commitment::ipa::OpeningProof;

use crate::{
    common::FULL_ROUNDS,
    shifted_value::{split_repr, type2_of_field},
};

type FpSpongeRef = ArithmeticSponge<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

/// The transcript witness of one wrap (Pallas) proof, as a step circuit
/// re-derives it. Raw challenges are 128-bit values in Fp (the step circuit
/// field); the deferred Tock (Fq) scalars are `Type2` split pairs.
pub struct StepWitness {
    pub beta_raw: Fp,
    pub gamma_raw: Fp,
    pub alpha_raw: Fp,
    pub zeta_raw: Fp,
    /// `sponge_digest_before_evaluations` (the Fp squeeze embedded in Fq —
    /// always lossless since `p < q`).
    pub sponge_digest: Fq,
    /// The wrap proof's IPA round prechallenges (raw 128-bit).
    pub bulletproof_prechallenges: Vec<Fp>,
    // Type2 split pairs `(s_div_2, s_odd)` of the deferred Fq scalars
    pub cip: (Fp, bool),
    pub b: (Fp, bool),
    pub perm: (Fp, bool),
    pub zeta_to_srs_length: (Fp, bool),
    pub zeta_to_domain_size: (Fp, bool),
    pub z1: (Fp, bool),
    pub z2: (Fp, bool),
}

/// The low 128 bits of an Fp element (a squeezed challenge).
fn low_128(x: Fp) -> Fp {
    let bits = x.into_bigint().to_bits_le();
    let mut acc = Fp::zero();
    for &b in bits[..128].iter().rev() {
        acc = acc + acc;
        if b {
            acc += Fp::one();
        }
    }
    acc
}

/// Replays the whole Fp-sponge transcript of a Pallas proof and derives the
/// step-circuit witness (see [`crate::wrap::wrap_witness`] for the mirrored
/// documentation; the differences are the Type2 split representatives and
/// their two-limb absorption).
#[allow(clippy::too_many_arguments)]
pub fn step_witness(
    max_poly_size: u64,
    domain_size: u64,
    domain_gen: Fq,
    proof: &ProverProof<Pallas, OpeningProof<Pallas, FULL_ROUNDS>, FULL_ROUNDS>,
    public_comm: &poly_commitment::commitment::PolyComm<Pallas>,
    vk_digest: Fp,
    combined_inner_product: Fq,
    zeta: Fq,
    evalscale: Fq,
    perm: Fq,
) -> StepWitness {
    use poly_commitment::commitment::b_poly;

    let params = <Pallas as KimchiCurve<FULL_ROUNDS>>::other_curve_sponge_params();
    let mut s = FpSpongeRef::new(params);
    let abpt = |s: &mut FpSpongeRef, p: &Pallas| {
        s.absorb(&[p.x]);
        s.absorb(&[p.y]);
    };

    // oracle transcript (base subset)
    s.absorb(&[vk_digest]);
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

    // fork: digest on a clone (Fp squeeze embedded in Fq — always fits)
    let sponge_digest = {
        let d: Fp = s.clone().squeeze();
        Fq::from_le_bytes_mod_order(&d.into_bigint().to_bytes_le())
    };

    // Type2 split representatives of the deferred scalars
    let t2 = |v: Fq| split_repr::<Fq, Fp>(type2_of_field(v));
    let cip = t2(combined_inner_product);
    let zeta_to_srs_length = zeta.pow([max_poly_size]);
    let zeta_to_domain_size = zeta.pow([domain_size]);

    // IPA transcript: absorb the split pair (two limbs — kimchi's absorb_fr
    // for the bigger scalar field), squeeze the group-map input, the rounds, c
    s.absorb(&[cip.0]);
    s.absorb(&[if cip.1 { Fp::one() } else { Fp::zero() }]);
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
    let endo_q = <Pallas as KimchiCurve<FULL_ROUNDS>>::endos().1;
    let chals: Vec<Fq> = prechallenges
        .iter()
        .map(|&raw| {
            let raw_fq = Fq::from_le_bytes_mod_order(&raw.into_bigint().to_bytes_le());
            crate::scalar_challenge::ScalarChallenge(raw_fq).to_field(endo_q)
        })
        .collect();
    let zetaw = zeta * domain_gen;
    let b_value = b_poly(&chals, zeta) + evalscale * b_poly(&chals, zetaw);

    StepWitness {
        beta_raw,
        gamma_raw,
        alpha_raw,
        zeta_raw,
        sponge_digest,
        bulletproof_prechallenges: prechallenges,
        cip,
        b: t2(b_value),
        perm: t2(perm),
        zeta_to_srs_length: t2(zeta_to_srs_length),
        zeta_to_domain_size: t2(zeta_to_domain_size),
        z1: t2(proof.proof.z1),
        z2: t2(proof.proof.z2),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mina_curves::pasta::PallasParameters;
    use mina_poseidon::sponge::{DefaultFqSponge, DefaultFrSponge};
    use poly_commitment::{
        commitment::{shift_scalar, PolyComm},
        SRS,
    };
    use snarky::{api::SnarkyCircuit, loc, FieldVar, RunState, SnarkyResult};

    type BaseSponge = DefaultFqSponge<PallasParameters, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;
    type ScalarSponge = DefaultFrSponge<Fq, PlonkSpongeConstantsKimchi, FULL_ROUNDS>;

    struct SmallCircuit {}
    impl SnarkyCircuit for SmallCircuit {
        type Curve = Pallas;
        type Proof = OpeningProof<Self::Curve, FULL_ROUNDS>;
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

    /// The replayed transcript witness matches kimchi's own oracles on a real
    /// Pallas proof, with the Type2 split conventions: raws map to the oracle
    /// field images, the split cip recomposes to kimchi's shift_scalar, and
    /// the prechallenges continue kimchi's own forked sponge.
    #[test]
    fn step_witness_matches_kimchi_oracles() {
        let circuit = SmallCircuit {};
        let (mut pi, ver) = circuit.compile_to_indexes().unwrap();
        let vi = &ver.index;
        let x = Fq::from(4u64);
        let z = x * x;
        let (proof, _) = pi.prove::<BaseSponge, ScalarSponge>(z, x, true).unwrap();

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
            .oracles::<BaseSponge, ScalarSponge, _>(vi, &public_comm, Some(&public_input))
            .unwrap();
        let oracles = &o.oracles;

        let w = step_witness(
            vi.max_poly_size as u64,
            vi.domain.size,
            vi.domain.group_gen,
            &proof,
            &public_comm,
            vi.digest::<BaseSponge>(),
            o.combined_inner_product,
            oracles.zeta,
            oracles.u,
            Fq::from(0u64), // perm not compared here
        );

        let endo_q = <Pallas as KimchiCurve<FULL_ROUNDS>>::endos().1;
        let to_fq = |x: Fp| Fq::from_le_bytes_mod_order(&x.into_bigint().to_bytes_le());
        assert_eq!(to_fq(w.beta_raw), oracles.beta, "beta");
        assert_eq!(to_fq(w.gamma_raw), oracles.gamma, "gamma");
        assert_eq!(
            crate::scalar_challenge::ScalarChallenge(to_fq(w.alpha_raw)).to_field(endo_q),
            oracles.alpha,
            "alpha raw -> field"
        );
        assert_eq!(
            crate::scalar_challenge::ScalarChallenge(to_fq(w.zeta_raw)).to_field(endo_q),
            oracles.zeta,
            "zeta raw -> field"
        );
        assert_eq!(w.sponge_digest, o.digest, "sponge digest");
        // the split cip recomposes to kimchi's shift_scalar (Type2 branch)
        let recomposed = {
            let half_fq = to_fq(w.cip.0);
            half_fq + half_fq + if w.cip.1 { Fq::one() } else { Fq::zero() }
        };
        assert_eq!(
            recomposed,
            shift_scalar::<Pallas>(o.combined_inner_product),
            "cip split recomposition"
        );
        // the prechallenges continue kimchi's own forked sponge
        let kimchi_chals = {
            use mina_poseidon::FqSponge as _;
            let mut sp = o.fq_sponge.clone();
            sp.absorb_fr(&[shift_scalar::<Pallas>(o.combined_inner_product)]);
            let _t = sp.challenge_fq();
            proof.proof.challenges::<BaseSponge>(&endo_q, &mut sp).chal
        };
        let our_chals: Vec<Fq> = w
            .bulletproof_prechallenges
            .iter()
            .map(|&raw| crate::scalar_challenge::ScalarChallenge(to_fq(raw)).to_field(endo_q))
            .collect();
        assert_eq!(our_chals, kimchi_chals, "IPA challenges");
        // b round-trips through the Type2 split
        use poly_commitment::commitment::b_poly;
        let zetaw = oracles.zeta * vi.domain.group_gen;
        let b_ref = b_poly(&kimchi_chals, oracles.zeta) + oracles.u * b_poly(&kimchi_chals, zetaw);
        let b_rec = {
            let half_fq = to_fq(w.b.0);
            crate::shifted_value::type2_to_field(
                half_fq + half_fq + if w.b.1 { Fq::one() } else { Fq::zero() },
            )
        };
        assert_eq!(b_rec, b_ref, "b split round-trip");
    }
}
