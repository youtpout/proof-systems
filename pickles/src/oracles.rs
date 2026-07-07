//! In-circuit derivation of the Fq-sponge oracles (`beta`, `gamma`, `alpha`,
//! `zeta`) — the first part of pickles' `incrementally_verify_proof` and the
//! step/wrap counterpart of kimchi's `to_batch` oracle section
//! (`kimchi/src/verifier.rs`, lines ~160–276).
//!
//! The Fq-sponge absorbs group elements (commitment coordinates) and squeezes
//! 128-bit challenges. Since a step circuit over `Fp` verifies a wrap proof
//! whose commitments are points with coordinates in `Fp`, the sponge is the
//! same [`crate::sponge::PoseidonSponge`] used everywhere else — only the
//! absorbed sequence differs (point coordinates instead of scalar
//! evaluations).
//!
//! Absorption order (no lookup / no optional gates):
//! ```text
//! absorb(vk_digest);
//! absorb_commitment(public_comm);
//! for w in w_comm { absorb_commitment(w) }
//! beta  = challenge();          // raw 128-bit
//! gamma = challenge();          // raw 128-bit
//! absorb_commitment(z_comm);
//! alpha = to_field(challenge()); // endo
//! absorb_commitment(t_comm);     // 7 chunks
//! zeta  = to_field(challenge()); // endo
//! ```

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{FieldVar, RunState, SnarkyResult};

use crate::challenge::squeeze_challenge;
use crate::scalar_challenge::scalar_to_field;
use crate::sponge::PoseidonSponge;

/// A commitment's affine coordinates `(x, y)` in the circuit field (a single
/// chunk); the point at infinity is encoded as `(0, 0)`, matching
/// `FqSponge::absorb_g`.
pub type PointVar<F> = (FieldVar<F>, FieldVar<F>);

/// The Fq-sponge oracles re-derived in-circuit. `beta`/`gamma` are the raw
/// 128-bit challenges; `alpha`/`zeta` are the endomorphism field images.
pub struct FqOracles<F: PrimeField> {
    pub beta: FieldVar<F>,
    pub gamma: FieldVar<F>,
    pub alpha: FieldVar<F>,
    pub zeta: FieldVar<F>,
}

/// Absorbs a commitment's chunks (each an affine point) into the sponge,
/// coordinate by coordinate — the in-circuit `absorb_commitment` / `absorb_g`.
pub(crate) fn absorb_commitment<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    sponge: &mut PoseidonSponge<F>,
    chunks: &[PointVar<F>],
) {
    for (x, y) in chunks {
        sponge.absorb(sys, loc.clone(), std::slice::from_ref(x));
        sponge.absorb(sys, loc.clone(), std::slice::from_ref(y));
    }
}

/// Re-derives the Fq-sponge oracles from the proof commitments (base subset:
/// no lookup, no optional gates). `vk_digest` is the base-field digest of the
/// verifier index (`index.digest`); `endo` is the scalar endomorphism
/// coefficient.
#[allow(clippy::too_many_arguments)]
pub fn derive_fq_oracles<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    vk_digest: &FieldVar<F>,
    public_comm: &[PointVar<F>],
    w_comm: &[Vec<PointVar<F>>],
    z_comm: &[PointVar<F>],
    t_comm: &[PointVar<F>],
    endo: F,
) -> SnarkyResult<FqOracles<F>> {
    let mut sponge = PoseidonSponge::new();

    // absorb the verifier-index digest
    sponge.absorb(sys, loc.clone(), std::slice::from_ref(vk_digest));

    // absorb the public-input commitment, then the witness commitments
    absorb_commitment(sys, loc.clone(), &mut sponge, public_comm);
    for w in w_comm {
        absorb_commitment(sys, loc.clone(), &mut sponge, w);
    }

    // beta, gamma (raw 128-bit challenges)
    let beta = squeeze_challenge(sys, loc.clone(), &mut sponge)?;
    let gamma = squeeze_challenge(sys, loc.clone(), &mut sponge)?;

    // absorb the permutation commitment, then sample alpha (endo)
    absorb_commitment(sys, loc.clone(), &mut sponge, z_comm);
    let alpha_chal = squeeze_challenge(sys, loc.clone(), &mut sponge)?;
    let alpha = scalar_to_field(sys, loc.clone(), &alpha_chal, endo)?;

    // absorb the quotient commitment, then sample zeta (endo)
    absorb_commitment(sys, loc.clone(), &mut sponge, t_comm);
    let zeta_chal = squeeze_challenge(sys, loc.clone(), &mut sponge)?;
    let zeta = scalar_to_field(sys, loc.clone(), &zeta_chal, endo)?;

    Ok(FqOracles {
        beta,
        gamma,
        alpha,
        zeta,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{AdditiveGroup, BigInteger, One, Zero};
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Vesta, VestaParameters};
    use mina_poseidon::poseidon::{ArithmeticSponge, Sponge as _};
    use mina_poseidon::sponge::ScalarChallenge;
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        sponge::{DefaultFqSponge, DefaultFrSponge},
    };
    use poly_commitment::ipa::OpeningProof;
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

    /// Out-of-circuit reference following the exact same absorb/squeeze order,
    /// over a plain `ArithmeticSponge<Fp>` (which `DuplexState` reproduces).
    fn reference_oracles(
        vk_digest: Fp,
        public_comm: &[(Fp, Fp)],
        w_comm: &[Vec<(Fp, Fp)>],
        z_comm: &[(Fp, Fp)],
        t_comm: &[(Fp, Fp)],
        endo: Fp,
    ) -> (Fp, Fp, Fp, Fp) {
        let mut s = RefSponge::new(Vesta::sponge_params());
        let absorb_c = |s: &mut RefSponge, chunks: &[(Fp, Fp)]| {
            for (x, y) in chunks {
                s.absorb(&[*x]);
                s.absorb(&[*y]);
            }
        };
        s.absorb(&[vk_digest]);
        absorb_c(&mut s, public_comm);
        for w in w_comm {
            absorb_c(&mut s, w);
        }
        let beta = lowest_128(s.squeeze());
        let gamma = lowest_128(s.squeeze());
        absorb_c(&mut s, z_comm);
        let alpha_chal = lowest_128(s.squeeze());
        let alpha = ScalarChallenge::new(alpha_chal).to_field(&endo);
        absorb_c(&mut s, t_comm);
        let zeta_chal = lowest_128(s.squeeze());
        let zeta = ScalarChallenge::new(zeta_chal).to_field(&endo);
        (beta, gamma, alpha, zeta)
    }

    struct OracleCircuit {
        vk_digest: Fp,
        public_comm: Vec<(Fp, Fp)>,
        w_comm: Vec<Vec<(Fp, Fp)>>,
        z_comm: Vec<(Fp, Fp)>,
        t_comm: Vec<(Fp, Fp)>,
        endo: Fp,
    }
    impl SnarkyCircuit for OracleCircuit {
        type Curve = Vesta;
        type Proof = OpeningProof<Self::Curve, { snarky::FULL_ROUNDS }>;
        type PrivateInput = ();
        type PublicInput = ();
        // ((beta, gamma), (alpha, zeta))
        type PublicOutput = ((FieldVar<Fp>, FieldVar<Fp>), (FieldVar<Fp>, FieldVar<Fp>));
        fn circuit(
            &self,
            sys: &mut RunState<Fp>,
            _p: Self::PublicInput,
            _pr: Option<&Self::PrivateInput>,
        ) -> SnarkyResult<Self::PublicOutput> {
            let wp = |sys: &mut RunState<Fp>, p: &[(Fp, Fp)]| -> SnarkyResult<Vec<PointVar<Fp>>> {
                let mut out = vec![];
                for &(x, y) in p {
                    out.push((
                        sys.compute(loc!(), move |_| x)?,
                        sys.compute(loc!(), move |_| y)?,
                    ));
                }
                Ok(out)
            };
            let vk: FieldVar<Fp> = sys.compute(loc!(), |_| self.vk_digest)?;
            let public_comm = wp(sys, &self.public_comm)?;
            let mut w_comm = vec![];
            for w in &self.w_comm {
                w_comm.push(wp(sys, w)?);
            }
            let z_comm = wp(sys, &self.z_comm)?;
            let t_comm = wp(sys, &self.t_comm)?;
            let o = derive_fq_oracles(
                sys,
                loc!(),
                &vk,
                &public_comm,
                &w_comm,
                &z_comm,
                &t_comm,
                self.endo,
            )?;
            Ok(((o.beta, o.gamma), (o.alpha, o.zeta)))
        }
    }

    /// In-circuit Fq-sponge oracles match the out-of-circuit reference on
    /// random commitment coordinates.
    #[test]
    fn fq_oracles_match_reference() {
        use ark_ff::UniformRand;
        let mut rng = o1_utils::tests::make_test_rng(None);
        let pt = |rng: &mut _| (Fp::rand(rng), Fp::rand(rng));
        let vk_digest = Fp::rand(&mut rng);
        let public_comm = vec![pt(&mut rng)];
        let w_comm: Vec<Vec<(Fp, Fp)>> = (0..15).map(|_| vec![pt(&mut rng)]).collect();
        let z_comm = vec![pt(&mut rng)];
        let t_comm: Vec<(Fp, Fp)> = (0..7).map(|_| pt(&mut rng)).collect();
        let (_, endo_r) = <Vesta as KimchiCurve<{ snarky::FULL_ROUNDS }>>::endos();

        let (beta, gamma, alpha, zeta) =
            reference_oracles(vk_digest, &public_comm, &w_comm, &z_comm, &t_comm, *endo_r);

        let circ = OracleCircuit {
            vk_digest,
            public_comm,
            w_comm,
            z_comm,
            t_comm,
            endo: *endo_r,
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        let ((b, g), (a, z)) = *out.clone();
        assert_eq!(b, beta, "beta");
        assert_eq!(g, gamma, "gamma");
        assert_eq!(a, alpha, "alpha");
        assert_eq!(z, zeta, "zeta");
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }
}
