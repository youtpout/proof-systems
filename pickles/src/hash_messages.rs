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
use mina_poseidon::poseidon::ArithmeticSpongeParams;
use snarky::{gadgets::curve::Point, Boolean, FieldVar, RunState, SnarkyResult};

use crate::{
    common::FULL_ROUNDS, composition_types::PlonkVerificationKeyEvals, sponge::PoseidonSponge,
};

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

/// Fixed-width variant of [`hash_messages_for_next_step_proof`] matching
/// OCaml's `hash_messages_for_next_step_proof_opt`. The verification key and
/// application state are absorbed normally; every accumulator coordinate and
/// challenge is then conditionally absorbed according to the branch's
/// checked proofs-verified mask.
pub fn hash_messages_for_next_step_proof_opt<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    sponge_after_index: &PoseidonSponge<F>,
    app_state: &[FieldVar<F>],
    challenge_polynomial_commitments: &[Point<F>],
    old_bulletproof_challenges: &[Vec<FieldVar<F>>],
    proofs_verified_mask: &[Boolean<F>],
) -> SnarkyResult<FieldVar<F>> {
    assert_eq!(
        challenge_polynomial_commitments.len(),
        old_bulletproof_challenges.len(),
        "hash_messages_for_next_step_proof_opt: one challenge vector per commitment"
    );
    assert_eq!(
        challenge_polynomial_commitments.len(),
        proofs_verified_mask.len(),
        "hash_messages_for_next_step_proof_opt: one mask bit per accumulator"
    );

    let mut prefix = sponge_after_index.clone();
    for value in app_state {
        prefix.absorb(sys, loc.clone(), std::slice::from_ref(value));
    }
    let mut sponge = crate::opt_sponge::OptSponge::from_sponge(prefix);
    for ((commitment, challenges), keep) in challenge_polynomial_commitments
        .iter()
        .zip(old_bulletproof_challenges)
        .zip(proofs_verified_mask)
    {
        sponge.absorb((keep.clone(), commitment.x.clone()));
        sponge.absorb((keep.clone(), commitment.y.clone()));
        for challenge in challenges {
            sponge.absorb((keep.clone(), challenge.clone()));
        }
    }
    sponge.squeeze(sys, loc)
}

/// Out-of-circuit mirror of [`hash_messages_for_next_step_proof`].
pub fn hash_messages_for_next_step_proof_ref<F: PrimeField>(
    params: &'static ArithmeticSpongeParams<F, FULL_ROUNDS>,
    dlog_plonk_index: &[(F, F)],
    app_state: &[F],
    challenge_polynomial_commitments: &[(F, F)],
    old_bulletproof_challenges: &[Vec<F>],
) -> F {
    use mina_poseidon::poseidon::Sponge as _;

    assert_eq!(
        challenge_polynomial_commitments.len(),
        old_bulletproof_challenges.len(),
        "hash_messages_for_next_step_proof_ref: one challenge vector per commitment"
    );

    let mut sponge = crate::sponge::make_sponge(params);
    for (x, y) in dlog_plonk_index {
        sponge.absorb(&[*x]);
        sponge.absorb(&[*y]);
    }
    for x in app_state {
        sponge.absorb(&[*x]);
    }
    for ((x, y), chals) in challenge_polynomial_commitments
        .iter()
        .zip(old_bulletproof_challenges)
    {
        sponge.absorb(&[*x]);
        sponge.absorb(&[*y]);
        for c in chals {
            sponge.absorb(&[*c]);
        }
    }
    sponge.squeeze()
}

/// Hashes a `messages_for_next_wrap_proof` accumulator
/// (`Wrap_hack.Checked.hash_messages_for_next_wrap_proof`): a fresh sponge
/// absorbs `dummy_challenges` (circuit constants padding the vector to
/// `Padded_length = 2` — empty when this circuit verifies the full width),
/// then the real old bulletproof challenges, then the challenge-polynomial
/// commitment's coordinates (`MessagesForNextWrapProof::to_field_elements`
/// order), and squeezes the digest.
///
/// The dummy vectors are `Dummy.Ipa.Wrap.challenges_computed` in OCaml — the
/// prover-side `Ro` constants, to be supplied when width < 2 (ported with the
/// prover; the OCaml precomputed sponge states are an in-circuit optimization
/// of exactly this front-padding absorption).
pub fn hash_messages_for_next_wrap_proof<F: PrimeField>(
    sys: &mut RunState<F>,
    loc: Cow<'static, str>,
    dummy_challenges: &[Vec<F>],
    old_bulletproof_challenges: &[Vec<FieldVar<F>>],
    challenge_polynomial_commitment: &Point<F>,
) -> FieldVar<F> {
    // The dummy prefix is constant, so its absorption happens out of
    // circuit (OCaml `Wrap_hack` caches this sponge state); only the
    // variable suffix costs Poseidon rows.
    let mut sponge = {
        use mina_poseidon::poseidon::{ArithmeticSponge, Sponge as _, SpongeState};
        let params = crate::sponge::params_for_field::<F>();
        let mut constant_sponge = ArithmeticSponge::<
            F,
            mina_poseidon::constants::PlonkSpongeConstantsKimchi,
            FULL_ROUNDS,
        >::new(params);
        for chals in dummy_challenges {
            for c in chals {
                constant_sponge.absorb(&[*c]);
            }
        }
        let absorbed = match constant_sponge.sponge_state {
            SpongeState::Absorbed(n) => n,
            SpongeState::Squeezed(_) => unreachable!("prefix only absorbs"),
        };
        PoseidonSponge::from_constant_state(
            [
                constant_sponge.state[0],
                constant_sponge.state[1],
                constant_sponge.state[2],
            ],
            absorbed,
        )
    };
    for chals in old_bulletproof_challenges {
        for c in chals {
            sponge.absorb(sys, loc.clone(), std::slice::from_ref(c));
        }
    }
    sponge.absorb(
        sys,
        loc.clone(),
        std::slice::from_ref(&challenge_polynomial_commitment.x),
    );
    sponge.absorb(
        sys,
        loc.clone(),
        std::slice::from_ref(&challenge_polynomial_commitment.y),
    );
    sponge.squeeze(sys, loc)
}

/// Out-of-circuit mirror of [`hash_messages_for_next_wrap_proof`].
pub fn hash_messages_for_next_wrap_proof_ref<F: PrimeField>(
    params: &'static ArithmeticSpongeParams<F, FULL_ROUNDS>,
    dummy_challenges: &[Vec<F>],
    old_bulletproof_challenges: &[Vec<F>],
    challenge_polynomial_commitment: (F, F),
) -> F {
    use mina_poseidon::poseidon::Sponge as _;

    let mut sponge = crate::sponge::make_sponge(params);
    for chals in dummy_challenges {
        for c in chals {
            sponge.absorb(&[*c]);
        }
    }
    for chals in old_bulletproof_challenges {
        for c in chals {
            sponge.absorb(&[*c]);
        }
    }
    sponge.absorb(&[challenge_polynomial_commitment.0]);
    sponge.absorb(&[challenge_polynomial_commitment.1]);
    sponge.squeeze()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::UniformRand;
    use kimchi::{
        circuits::wires::{COLUMNS, PERMUTS},
        curve::KimchiCurve,
    };
    use mina_curves::pasta::{Fp, Fq, Pallas, Vesta, VestaParameters};
    use mina_poseidon::{
        constants::PlonkSpongeConstantsKimchi,
        poseidon::{ArithmeticSponge, Sponge as _},
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
        mask: Option<Vec<bool>>,
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
            if let Some(mask) = &self.mask {
                let mask = mask
                    .iter()
                    .map(|&keep| sys.compute(loc!(), move |_| keep))
                    .collect::<SnarkyResult<Vec<Boolean<Fp>>>>()?;
                hash_messages_for_next_step_proof_opt(
                    sys,
                    loc!(),
                    &after_index,
                    &app_state,
                    &cpcs,
                    &old_chals,
                    &mask,
                )
            } else {
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

        let expected = hash_messages_for_next_step_proof_ref(
            Vesta::sponge_params(),
            &vk_comms,
            &app_state,
            &cpcs,
            &old_chals,
        );

        let circ = HashCircuit {
            vk_comms,
            app_state,
            cpcs,
            old_chals,
            mask: None,
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        assert_eq!(*out, expected);
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }

    #[test]
    fn optional_step_hash_matches_filtered_reference() {
        let mut rng = o1_utils::tests::make_test_rng(None);
        let pt = |rng: &mut _| {
            let p = (Pallas::generator() * Fq::rand(rng)).into_affine();
            (p.x, p.y)
        };
        let vk_comms: Vec<(Fp, Fp)> = (0..PERMUTS + COLUMNS + 6).map(|_| pt(&mut rng)).collect();
        let app_state = vec![Fp::rand(&mut rng)];
        let cpcs: Vec<(Fp, Fp)> = (0..2).map(|_| pt(&mut rng)).collect();
        let old_chals: Vec<Vec<Fp>> = (0..2)
            .map(|_| {
                (0..crate::common::TICK_ROUNDS)
                    .map(|_| Fp::rand(&mut rng))
                    .collect()
            })
            .collect();

        for mask in [vec![false, false], vec![false, true], vec![true, true]] {
            let filtered_cpcs: Vec<_> = cpcs
                .iter()
                .zip(&mask)
                .filter_map(|(&value, &keep)| keep.then_some(value))
                .collect();
            let filtered_chals: Vec<_> = old_chals
                .iter()
                .zip(&mask)
                .filter_map(|(value, &keep)| keep.then_some(value.clone()))
                .collect();
            let expected = hash_messages_for_next_step_proof_ref(
                Vesta::sponge_params(),
                &vk_comms,
                &app_state,
                &filtered_cpcs,
                &filtered_chals,
            );
            let circ = HashCircuit {
                vk_comms: vk_comms.clone(),
                app_state: app_state.clone(),
                cpcs: cpcs.clone(),
                old_chals: old_chals.clone(),
                mask: Some(mask.clone()),
            };
            let (mut pi, _) = circ.compile_to_indexes().unwrap();
            let (_, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
            assert_eq!(*out, expected, "mask = {mask:?}");
        }
    }

    struct WrapHashCircuit {
        dummy_chals: Vec<Vec<Fp>>,
        old_chals: Vec<Vec<Fp>>,
        cpc: (Fp, Fp),
    }

    impl SnarkyCircuit for WrapHashCircuit {
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
            let mut old_chals = vec![];
            for v in &self.old_chals {
                let mut row = vec![];
                for &c in v {
                    row.push(sys.compute(loc!(), move |_| c)?);
                }
                old_chals.push(row);
            }
            let cpc = Point::new(
                sys.compute(loc!(), |_| self.cpc.0)?,
                sys.compute(loc!(), |_| self.cpc.1)?,
            );
            Ok(hash_messages_for_next_wrap_proof(
                sys,
                loc!(),
                &self.dummy_chals,
                &old_chals,
                &cpc,
            ))
        }
    }

    /// `hash_messages_for_next_wrap_proof` == the out-of-circuit sponge over
    /// dummy padding, real challenges, then the commitment coordinates.
    #[test]
    fn wrap_hash_matches_reference() {
        let mut rng = o1_utils::tests::make_test_rng(None);
        let dummy_chals: Vec<Vec<Fp>> = vec![(0..crate::common::TOCK_ROUNDS)
            .map(|_| Fp::rand(&mut rng))
            .collect()];
        let old_chals: Vec<Vec<Fp>> = vec![(0..crate::common::TOCK_ROUNDS)
            .map(|_| Fp::rand(&mut rng))
            .collect()];
        let cpc = {
            let p = (Pallas::generator() * Fq::rand(&mut rng)).into_affine();
            (p.x, p.y)
        };

        let mut s = RefSponge::new(Vesta::sponge_params());
        for v in dummy_chals.iter().chain(&old_chals) {
            for c in v {
                s.absorb(&[*c]);
            }
        }
        s.absorb(&[cpc.0]);
        s.absorb(&[cpc.1]);
        let expected = s.squeeze();
        assert_eq!(
            hash_messages_for_next_wrap_proof_ref(
                Vesta::sponge_params(),
                &dummy_chals,
                &old_chals,
                cpc,
            ),
            expected
        );

        let circ = WrapHashCircuit {
            dummy_chals,
            old_chals,
            cpc,
        };
        let (mut pi, ver) = circ.compile_to_indexes().unwrap();
        let (proof, out) = pi.prove::<BaseSponge, ScalarSponge>((), (), true).unwrap();
        assert_eq!(*out, expected);
        ver.verify::<BaseSponge, ScalarSponge>(proof, (), *out);
    }
}
