//! In-circuit hashing of `messages_for_next_step_proof`
//! (`step_verifier.ml::hash_messages_for_next_step_proof` /
//! `sponge_after_index`).
//!
//! The digest commits the step statement to the recursion accumulator: the
//! wrap verification key (absorbed first, and shared by every proof — hence
//! the reusable `sponge_after_index` state), the application state, and per
//! previous proof its challenge-polynomial commitment followed by its old
//! bulletproof challenges.
//!
//! Base subset: every previous proof is real (`proofs_verified_mask` all
//! true), so the optional-sponge masking of
//! `hash_messages_for_next_step_proof_opt` degenerates to plain absorption.

use std::borrow::Cow;

use ark_ff::PrimeField;
use snarky::{gadgets::curve::Point, FieldVar, RunState, SnarkyResult};

use crate::composition_types::PlonkVerificationKeyEvals;
use crate::sponge::PoseidonSponge;

/// A fresh sponge with the wrap verification key absorbed
/// (`index_to_field_elements` order: sigma, coefficients, generic, psm,
/// complete_add, mul, emul, endomul_scalar; each commitment as `x, y`).
pub fn sponge_after_index<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    vk: &PlonkVerificationKeyEvals<Point<F>>,
) -> PoseidonSponge<F> {
    let mut sponge = PoseidonSponge::new();
    for comm in vk.to_list() {
        sponge.absorb(sys, loc.clone(), std::slice::from_ref(&comm.x));
        sponge.absorb(sys, loc.clone(), std::slice::from_ref(&comm.y));
    }
    sponge
}

/// Hashes the `messages_for_next_step_proof` accumulator: continues a copy of
/// [`sponge_after_index`] with `to_field_elements_without_index` — the
/// application state, then per previous proof its challenge-polynomial
/// commitment (`x, y`) followed by its old bulletproof challenges — and
/// squeezes the digest.
pub fn hash_messages_for_next_step_proof<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    sponge_after_index: &PoseidonSponge<F>,
    app_state: &[FieldVar<F>],
    challenge_polynomial_commitments: &[Point<F>],
    old_bulletproof_challenges: &[Vec<FieldVar<F>>],
) -> SnarkyResult<FieldVar<F>> {
    assert_eq!(
        challenge_polynomial_commitments.len(),
        old_bulletproof_challenges.len(),
        "hash_messages_for_next_step_proof: one challenge vector per commitment"
    );

    let mut sponge = sponge_after_index.clone();
    for x in app_state {
        sponge.absorb(sys, loc.clone(), std::slice::from_ref(x));
    }
    for (comm, chals) in challenge_polynomial_commitments
        .iter()
        .zip(old_bulletproof_challenges)
    {
        sponge.absorb(sys, loc.clone(), std::slice::from_ref(&comm.x));
        sponge.absorb(sys, loc.clone(), std::slice::from_ref(&comm.y));
        for c in chals {
            sponge.absorb(sys, loc.clone(), std::slice::from_ref(c));
        }
    }
    Ok(sponge.squeeze(sys, loc))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::UniformRand;
    use kimchi::circuits::wires::{COLUMNS, PERMUTS};
    use kimchi::curve::KimchiCurve;
    use mina_curves::pasta::{Fp, Fq, Pallas, Vesta, VestaParameters};
    use mina_poseidon::poseidon::{ArithmeticSponge, Sponge as _};
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

    struct HashCircuit {
        vk_comms: Vec<(Fp, Fp)>,
        app_state: Vec<Fp>,
        cpcs: Vec<(Fp, Fp)>,
        old_chals: Vec<Vec<Fp>>,
    }

    impl SnarkyCircuit for HashCircuit {
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
        ) -> SnarkyResult<Self::PublicOutput> {
            let mkpt = |sys: &mut RunState<Fp>, p: (Fp, Fp)| -> SnarkyResult<Point<Fp>> {
                Ok(Point::new(
                    sys.compute(loc!(), move |_| p.0)?,
                    sys.compute(loc!(), move |_| p.1)?,
                ))
            };
            let mut comms = vec![];
            for &p in &self.vk_comms {
                comms.push(mkpt(sys, p)?);
            }
            // rebuild the vk struct from the flat to_list order
            let mut it = comms.into_iter();
            let vk = PlonkVerificationKeyEvals {
                sigma_comm: (0..PERMUTS).map(|_| it.next().unwrap()).collect(),
                coefficients_comm: (0..COLUMNS).map(|_| it.next().unwrap()).collect(),
                generic_comm: it.next().unwrap(),
                psm_comm: it.next().unwrap(),
                complete_add_comm: it.next().unwrap(),
                mul_comm: it.next().unwrap(),
                emul_comm: it.next().unwrap(),
                endomul_scalar_comm: it.next().unwrap(),
            };
            let mut app_state = vec![];
            for &x in &self.app_state {
                app_state.push(sys.compute(loc!(), move |_| x)?);
            }
            let mut cpcs = vec![];
            for &p in &self.cpcs {
                cpcs.push(mkpt(sys, p)?);
            }
            let mut old_chals = vec![];
            for v in &self.old_chals {
                let mut row = vec![];
                for &c in v {
                    row.push(sys.compute(loc!(), move |_| c)?);
                }
                old_chals.push(row);
            }

            let after_index = sponge_after_index(sys, loc!(), &vk);
            hash_messages_for_next_step_proof(
                sys,
                loc!(),
                &after_index,
                &app_state,
                &cpcs,
                &old_chals,
            )
        }
    }

    /// The in-circuit digest equals the out-of-circuit mirror over
    /// `ArithmeticSponge<Fp>` following the same absorption order (VK
    /// commitments, app state, then commitment + challenges per proof).
    #[test]
    fn hash_messages_matches_reference() {
        let mut rng = o1_utils::tests::make_test_rng(None);
        let pt = |rng: &mut _| {
            let p = (Pallas::generator() * Fq::rand(rng)).into_affine();
            (p.x, p.y)
        };

        let vk_comms: Vec<(Fp, Fp)> = (0..PERMUTS + COLUMNS + 6).map(|_| pt(&mut rng)).collect();
        let app_state: Vec<Fp> = (0..3).map(|_| Fp::rand(&mut rng)).collect();
        let cpcs: Vec<(Fp, Fp)> = (0..2).map(|_| pt(&mut rng)).collect();
        let old_chals: Vec<Vec<Fp>> = (0..2)
            .map(|_| {
                (0..crate::common::TICK_ROUNDS)
                    .map(|_| Fp::rand(&mut rng))
                    .collect()
            })
            .collect();

        // out-of-circuit mirror
        let mut s = RefSponge::new(Vesta::sponge_params());
        for (x, y) in &vk_comms {
            s.absorb(&[*x]);
            s.absorb(&[*y]);
        }
        for x in &app_state {
            s.absorb(&[*x]);
        }
        for ((x, y), chals) in cpcs.iter().zip(&old_chals) {
            s.absorb(&[*x]);
            s.absorb(&[*y]);
            for c in chals {
                s.absorb(&[*c]);
            }
        }
        let expected = s.squeeze();

        let circ = HashCircuit {
            vk_comms,
            app_state,
            cpcs,
            old_chals,
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        assert_eq!(*out, expected);
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }
}
