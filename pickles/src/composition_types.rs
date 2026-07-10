//! The statement types threaded through the pickles recursion
//! (port of `composition_types/composition_types.ml`,
//! `bulletproof_challenge.ml`, `branch_data.ml` and the `Features` record of
//! `plonk_types.ml`).
//!
//! Like the OCaml, every type is generic over the *representations* of its
//! leaves (field element, challenge, boolean, ...), so the same structure
//! serves both the out-of-circuit values and the in-circuit variables.

/// The per-circuit optional-gate flags.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Features<Bool> {
    pub range_check0: Bool,
    pub range_check1: Bool,
    pub foreign_field_add: Bool,
    pub foreign_field_mul: Bool,
    pub xor: Bool,
    pub rot: Bool,
    pub lookup: Bool,
    pub runtime_tables: Bool,
}

impl<Bool: Clone> Features<Bool> {
    pub fn of_bool(b: Bool) -> Self {
        Self {
            range_check0: b.clone(),
            range_check1: b.clone(),
            foreign_field_add: b.clone(),
            foreign_field_mul: b.clone(),
            xor: b.clone(),
            rot: b.clone(),
            lookup: b.clone(),
            runtime_tables: b,
        }
    }

    pub fn map<B2>(&self, mut f: impl FnMut(&Bool) -> B2) -> Features<B2> {
        Features {
            range_check0: f(&self.range_check0),
            range_check1: f(&self.range_check1),
            foreign_field_add: f(&self.foreign_field_add),
            foreign_field_mul: f(&self.foreign_field_mul),
            xor: f(&self.xor),
            rot: f(&self.rot),
            lookup: f(&self.lookup),
            runtime_tables: f(&self.runtime_tables),
        }
    }

    /// `Plonk_types.Features.to_data` order.
    pub fn to_data(&self) -> [Bool; 8] {
        [
            self.range_check0.clone(),
            self.range_check1.clone(),
            self.foreign_field_add.clone(),
            self.foreign_field_mul.clone(),
            self.xor.clone(),
            self.rot.clone(),
            self.lookup.clone(),
            self.runtime_tables.clone(),
        ]
    }

    /// Inverse of [`Features::to_data`].
    pub fn from_data(
        [
            range_check0,
            range_check1,
            foreign_field_add,
            foreign_field_mul,
            xor,
            rot,
            lookup,
            runtime_tables,
        ]: [Bool; 8],
    ) -> Self {
        Self {
            range_check0,
            range_check1,
            foreign_field_add,
            foreign_field_mul,
            xor,
            rot,
            lookup,
            runtime_tables,
        }
    }
}

impl Features<bool> {
    /// `Plonk_types.Features.none_bool` — no optional gate.
    pub fn none() -> Self {
        Self::of_bool(false)
    }
}

/// A challenge from the inner-product argument
/// (`bulletproof_challenge.ml`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BulletproofChallenge<Chal> {
    pub prechallenge: Chal,
}

/// How many previous proofs a step branch verifies (pickles is specialized
/// to at most 2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofsVerified {
    N0,
    N1,
    N2,
}

impl ProofsVerified {
    pub fn to_usize(self) -> usize {
        match self {
            ProofsVerified::N0 => 0,
            ProofsVerified::N1 => 1,
            ProofsVerified::N2 => 2,
        }
    }

    pub fn from_usize(n: usize) -> Self {
        match n {
            0 => ProofsVerified::N0,
            1 => ProofsVerified::N1,
            2 => ProofsVerified::N2,
            _ => panic!("ProofsVerified: expected 0, 1 or 2"),
        }
    }

    /// Pickles' fixed-width, front-padded proof mask.
    pub fn prefix_mask(self) -> [bool; crate::common::MAX_PROOFS_VERIFIED] {
        match self {
            ProofsVerified::N0 => [false, false],
            ProofsVerified::N1 => [false, true],
            ProofsVerified::N2 => [true, true],
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofSlot<T> {
    Dummy,
    Proof(T),
}

pub fn front_pad_proof_slots<T>(
    proofs: Vec<T>,
) -> [ProofSlot<T>; crate::common::MAX_PROOFS_VERIFIED] {
    let proofs_verified = ProofsVerified::from_usize(proofs.len());
    let mut proofs = proofs.into_iter();
    std::array::from_fn(|i| {
        if proofs_verified.prefix_mask()[i] {
            ProofSlot::Proof(proofs.next().expect("mask and proof count agree"))
        } else {
            ProofSlot::Dummy
        }
    })
}

/// Data identifying which step branch was verified (`branch_data.ml`).
/// `domain_log2` is the log2 of the step circuit's domain size.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BranchData {
    pub proofs_verified: ProofsVerified,
    pub domain_log2: u8,
}

impl BranchData {
    /// Packs into a single field element (`branch_data.ml`, `pack`): the low 2
    /// bits are `proofs_verified`, the next 8 bits are `domain_log2`, i.e.
    /// `domain_log2·4 + proofs_verified`.
    pub fn pack<F: ark_ff::PrimeField>(&self) -> F {
        let pv = self.proofs_verified.to_usize() as u64;
        F::from(u64::from(self.domain_log2)) * F::from(4u64) + F::from(pv)
    }

    /// Unpacks a branch-data field element (`branch_data.ml`, `unpack`): low
    /// two bits are `proofs_verified`, next eight bits are `domain_log2`.
    pub fn unpack<F: ark_ff::PrimeField>(x: F) -> Self {
        use ark_ff::BigInteger;

        let bits = x.into_bigint().to_bits_le();
        let pv = usize::from(bits[0]) | (usize::from(bits[1]) << 1);
        let mut domain_log2 = 0u8;
        for i in 0..8 {
            if bits[2 + i] {
                domain_log2 |= 1 << i;
            }
        }
        Self {
            proofs_verified: ProofsVerified::from_usize(pv),
            domain_log2,
        }
    }
}

pub mod plonk {
    use super::Features;

    /// The minimal PLONK verification challenges
    /// (`Deferred_values.Plonk.Minimal`): what the verifier re-derives from
    /// the transcript before computing the derived scalars.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Minimal<Challenge, ScalarChallenge, Bool> {
        pub alpha: ScalarChallenge,
        pub beta: Challenge,
        pub gamma: Challenge,
        pub zeta: ScalarChallenge,
        pub joint_combiner: Option<ScalarChallenge>,
        pub feature_flags: Features<Bool>,
    }

    /// The derived PLONK scalars (`Deferred_values.Plonk.In_circuit`): the
    /// minimal challenges plus the values `derive_plonk` computes
    /// (`zeta_to_srs_length`, `zeta_to_domain_size`, `perm`). `Challenge` and
    /// the derived scalars share the circuit field.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct InCircuit<Fp, ScalarChallenge, Bool> {
        pub alpha: ScalarChallenge,
        pub beta: Fp,
        pub gamma: Fp,
        pub zeta: ScalarChallenge,
        pub zeta_to_srs_length: Fp,
        pub zeta_to_domain_size: Fp,
        pub perm: Fp,
        pub feature_flags: Features<Bool>,
        pub joint_combiner: Option<ScalarChallenge>,
    }
}

/// The values whose verification is deferred to the other side of the cycle
/// (they live in the "wrong" field for the current circuit).
///
/// `BranchData` is [`super::BranchData`]-shaped on the step side and `()` on
/// the wrap side (`Deferred_values` in `composition_types.ml`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeferredValues<Plonk, Fp, ScalarChallenge, BpChals, BranchData> {
    pub plonk: Plonk,
    /// `sum_{i < num_evaluation_points} sum_{j < num_polys} r^i xi^j f_j(pt_i)`
    pub combined_inner_product: Fp,
    /// `b = challenge_poly(zeta) + r * challenge_poly(omega * zeta)` where
    /// `challenge_poly(x) = prod_i (1 + bp_challenges[i] * x^{2^{k-1-i}})`
    pub b: Fp,
    /// The challenge used for combining polynomials.
    pub xi: ScalarChallenge,
    /// The challenges from the partially-verified inner-product argument.
    pub bulletproof_challenges: BpChals,
    /// Which step branch was verified (step side only).
    pub branch_data: BranchData,
}

/// An unfinalized dlog-based proof (`unfinalized.ml`): the wrap proof state
/// carried through a step circuit, with a flag telling whether it is
/// expected to verify (false in base cases).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Unfinalized<Plonk, Fp, ScalarChallenge, BpChals, Digest, Bool> {
    pub deferred_values: DeferredValues<Plonk, Fp, ScalarChallenge, BpChals, ()>,
    pub should_finalize: Bool,
    pub sponge_digest_before_evaluations: Digest,
}

pub mod wrap {
    use super::{plonk, BranchData, BulletproofChallenge, DeferredValues};
    use crate::scalar_challenge::ScalarChallenge;
    use ark_ff::PrimeField;

    /// Flattens the wrap statement's deferred proof state to field elements in
    /// the `to_data` order (`composition_types.ml:815`):
    /// `fp[5]` (combined_inner_product, b, zeta_to_srs_length,
    /// zeta_to_domain_size, perm), `challenge[2]` (beta, gamma),
    /// `scalar_challenge[3]` (alpha, zeta, xi), `digest[3]`
    /// (sponge_digest_before_evaluations, messages_for_next_wrap_proof,
    /// messages_for_next_step_proof), `bulletproof_challenges[16]`,
    /// `index[1]` (branch_data), `feature_flags[8]`.
    ///
    /// Base case: no `joint_combiner`. The two `messages_for_next_*` are passed
    /// as their in-circuit digests. This is the public input the wrap circuit
    /// commits to.
    #[allow(clippy::too_many_arguments)]
    pub fn wrap_statement_to_field_elements<F: PrimeField>(
        plonk: &plonk::InCircuit<F, ScalarChallenge<F>, bool>,
        combined_inner_product: F,
        b: F,
        xi: &ScalarChallenge<F>,
        bulletproof_challenges: &[BulletproofChallenge<ScalarChallenge<F>>],
        branch_data: &BranchData,
        sponge_digest_before_evaluations: F,
        messages_for_next_wrap_proof_digest: F,
        messages_for_next_step_proof_digest: F,
    ) -> Vec<F> {
        let mut out = Vec::with_capacity(38);
        // fp (5)
        out.push(combined_inner_product);
        out.push(b);
        out.push(plonk.zeta_to_srs_length);
        out.push(plonk.zeta_to_domain_size);
        out.push(plonk.perm);
        // challenge (2)
        out.push(plonk.beta);
        out.push(plonk.gamma);
        // scalar_challenge (3): alpha, zeta, xi
        out.push(plonk.alpha.0);
        out.push(plonk.zeta.0);
        out.push(xi.0);
        // digest (3)
        out.push(sponge_digest_before_evaluations);
        out.push(messages_for_next_wrap_proof_digest);
        out.push(messages_for_next_step_proof_digest);
        // bulletproof_challenges (16)
        for c in bulletproof_challenges {
            out.push(c.prechallenge.0);
        }
        // index (1): branch_data
        out.push(branch_data.pack::<F>());
        // feature_flags (8) — Plonk_types.Features.to_data order
        for flag in plonk.feature_flags.to_data() {
            out.push(if flag { F::one() } else { F::zero() });
        }
        out
    }

    /// The wrap statement in the exact o1js/Mina network layout: the 40-slot
    /// public input of jsoo Pickles wrap circuits (`Wrap.Statement.In_circuit`
    /// spec instantiated by o1js with `Maybe` feature flags):
    ///
    /// - 5 fp (Type1 shifted values, one slot each: an Fp element fits in Fq)
    /// - 2 challenges (beta, gamma), 3 scalar challenges (alpha, zeta, xi)
    /// - 3 digests (sponge, messages_for_next_wrap, messages_for_next_step)
    /// - **16** bulletproof challenges — padded to `Tick.Rounds`, NOT to the
    ///   step circuit's domain: Mina proves over full-size SRSes so step IPA
    ///   proofs always have 16 rounds
    /// - 1 packed branch_data
    /// - 8 feature-flag booleans (public slots because o1js compiles with
    ///   `Maybe` flags)
    /// - 2 joint-combiner slots (opt flag boolean + scalar challenge), zero
    ///   for programs without lookups
    ///
    /// Our internal pipeline still uses the compact
    /// [`wrap_statement_to_field_elements`] (`22 + rounds` slots); switching
    /// the wrap circuit's public input to this layout is the statement half
    /// of the wrap parity work.
    #[allow(clippy::too_many_arguments)]
    pub fn wrap_statement_to_field_elements_ocaml<F: PrimeField>(
        plonk: &plonk::InCircuit<F, ScalarChallenge<F>, bool>,
        combined_inner_product: F,
        b: F,
        xi: &ScalarChallenge<F>,
        bulletproof_challenges: &[BulletproofChallenge<ScalarChallenge<F>>],
        dummy_bulletproof_challenge: &ScalarChallenge<F>,
        branch_data: &BranchData,
        sponge_digest_before_evaluations: F,
        messages_for_next_wrap_proof_digest: F,
        messages_for_next_step_proof_digest: F,
    ) -> Vec<F> {
        const TICK_ROUNDS: usize = crate::common::TICK_ROUNDS;
        assert!(bulletproof_challenges.len() <= TICK_ROUNDS);
        let mut out = Vec::with_capacity(40);
        // fp (5)
        out.push(combined_inner_product);
        out.push(b);
        out.push(plonk.zeta_to_srs_length);
        out.push(plonk.zeta_to_domain_size);
        out.push(plonk.perm);
        // challenge (2)
        out.push(plonk.beta);
        out.push(plonk.gamma);
        // scalar_challenge (3): alpha, zeta, xi
        out.push(plonk.alpha.0);
        out.push(plonk.zeta.0);
        out.push(xi.0);
        // digest (3)
        out.push(sponge_digest_before_evaluations);
        out.push(messages_for_next_wrap_proof_digest);
        out.push(messages_for_next_step_proof_digest);
        // bulletproof_challenges (16), padded in FRONT like
        // `Vector.extend_front` pads Mina's step challenges
        for _ in bulletproof_challenges.len()..TICK_ROUNDS {
            out.push(dummy_bulletproof_challenge.0);
        }
        for c in bulletproof_challenges {
            out.push(c.prechallenge.0);
        }
        // index (1): branch_data
        out.push(branch_data.pack::<F>());
        // feature_flags (8) — public boolean slots in o1js (`Maybe` flags)
        for flag in plonk.feature_flags.to_data() {
            out.push(if flag { F::one() } else { F::zero() });
        }
        // joint_combiner opt (2): flag boolean + scalar challenge
        out.push(F::zero());
        out.push(match &plonk.joint_combiner {
            Some(joint_combiner) => joint_combiner.0,
            None => F::zero(),
        });
        debug_assert_eq!(out.len(), 40);
        out
    }

    /// The wrap proof state (`Wrap.Proof_state`).
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct ProofState<Plonk, Fp, ScalarChallenge, BpChals, Digest, MessagesForNextWrap> {
        pub deferred_values: DeferredValues<Plonk, Fp, ScalarChallenge, BpChals, ()>,
        pub sponge_digest_before_evaluations: Digest,
        /// The accumulator state passed to the next wrap proof.
        pub messages_for_next_wrap_proof: MessagesForNextWrap,
    }

    /// The full wrap statement (`Wrap.Statement`): what a wrap proof proves.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Statement<ProofState, MessagesForNextStep> {
        pub proof_state: ProofState,
        pub messages_for_next_step_proof: MessagesForNextStep,
    }

    /// The accumulator threaded to the next wrap proof
    /// (`Messages_for_next_wrap_proof`).
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct MessagesForNextWrapProof<G1, BpChals> {
        /// The commitment to the previous challenge polynomial (`sg`).
        pub challenge_polynomial_commitment: G1,
        /// The bulletproof challenges of the previous proof.
        pub old_bulletproof_challenges: BpChals,
    }

    impl<G1, F: Clone> MessagesForNextWrapProof<G1, Vec<Vec<F>>> {
        /// Serialises to field elements for hashing (`to_field_elements`):
        /// the flattened old challenges, then the commitment coordinates.
        pub fn to_field_elements(&self, g1_to_field_elements: impl Fn(&G1) -> Vec<F>) -> Vec<F> {
            let mut out: Vec<F> = self
                .old_bulletproof_challenges
                .iter()
                .flat_map(|c| c.iter().cloned())
                .collect();
            out.extend(g1_to_field_elements(&self.challenge_polynomial_commitment));
            out
        }
    }
}

pub mod step {
    use super::{plonk, BulletproofChallenge};
    use crate::scalar_challenge::ScalarChallenge;
    use ark_ff::PrimeField;

    /// Flattens one unfinalized per-proof state to field elements in the
    /// `Step.Proof_state.Per_proof.In_circuit.to_data` order
    /// (`composition_types.ml:1223`): `fq[5]` (combined_inner_product, b,
    /// zeta_to_srs_length, zeta_to_domain_size, perm), `digest[1]`
    /// (sponge_digest_before_evaluations), `challenge[2]` (beta, gamma),
    /// `scalar_challenge[3]` (alpha, zeta, xi),
    /// `bulletproof_challenges[TOCK_ROUNDS]`, `bool[1]` (should_finalize).
    ///
    /// Note the digest comes *second* here, unlike the wrap statement where the
    /// digests come after the scalar challenges. The step side's `Plonk` has no
    /// feature flags or joint combiner in its layout (they are wrap-only), so
    /// those fields of [`plonk::InCircuit`] are ignored.
    #[allow(clippy::too_many_arguments)]
    pub fn unfinalized_to_field_elements<F: PrimeField>(
        plonk: &plonk::InCircuit<F, ScalarChallenge<F>, bool>,
        combined_inner_product: F,
        b: F,
        xi: &ScalarChallenge<F>,
        bulletproof_challenges: &[BulletproofChallenge<ScalarChallenge<F>>],
        sponge_digest_before_evaluations: F,
        should_finalize: bool,
    ) -> Vec<F> {
        let mut out = Vec::with_capacity(5 + 1 + 2 + 3 + bulletproof_challenges.len() + 1);
        // fq (5)
        out.push(combined_inner_product);
        out.push(b);
        out.push(plonk.zeta_to_srs_length);
        out.push(plonk.zeta_to_domain_size);
        out.push(plonk.perm);
        // digest (1)
        out.push(sponge_digest_before_evaluations);
        // challenge (2)
        out.push(plonk.beta);
        out.push(plonk.gamma);
        // scalar_challenge (3): alpha, zeta, xi
        out.push(plonk.alpha.0);
        out.push(plonk.zeta.0);
        out.push(xi.0);
        // bulletproof_challenges (TOCK_ROUNDS = 15)
        for c in bulletproof_challenges {
            out.push(c.prechallenge.0);
        }
        // bool (1)
        out.push(if should_finalize { F::one() } else { F::zero() });
        out
    }

    /// Flattens the step statement to field elements in the
    /// `Step.Statement.to_data` order (`composition_types.ml:1355`): each
    /// unfinalized proof (already flattened by
    /// [`unfinalized_to_field_elements`]), then the
    /// `messages_for_next_step_proof` digest, then one
    /// `messages_for_next_wrap_proof` digest per (max) proof verified.
    /// This is the public input the step circuit commits to.
    pub fn step_statement_to_field_elements<F: PrimeField>(
        unfinalized_proofs: &[Vec<F>],
        messages_for_next_step_proof_digest: F,
        messages_for_next_wrap_proof_digests: &[F],
    ) -> Vec<F> {
        let mut out = Vec::new();
        for u in unfinalized_proofs {
            out.extend(u.iter().copied());
        }
        out.push(messages_for_next_step_proof_digest);
        out.extend(messages_for_next_wrap_proof_digests.iter().copied());
        out
    }
}

/// The verification-key commitments threaded through the recursion
/// (`Plonk_verification_key_evals`): the wrap-circuit VK the step circuits
/// verify proofs against.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlonkVerificationKeyEvals<Comm> {
    /// The `PERMUTS` permutation commitments.
    pub sigma_comm: Vec<Comm>,
    /// The `COLUMNS` coefficient commitments.
    pub coefficients_comm: Vec<Comm>,
    pub generic_comm: Comm,
    pub psm_comm: Comm,
    pub complete_add_comm: Comm,
    pub mul_comm: Comm,
    pub emul_comm: Comm,
    pub endomul_scalar_comm: Comm,
}

impl<Comm> PlonkVerificationKeyEvals<Comm> {
    /// The commitments in the canonical `index_to_field_elements` order:
    /// sigma, coefficients, then the six named selectors.
    pub fn to_list(&self) -> Vec<&Comm> {
        let mut v: Vec<&Comm> = self.sigma_comm.iter().collect();
        v.extend(self.coefficients_comm.iter());
        v.push(&self.generic_comm);
        v.push(&self.psm_comm);
        v.push(&self.complete_add_comm);
        v.push(&self.mul_comm);
        v.push(&self.emul_comm);
        v.push(&self.endomul_scalar_comm);
        v
    }
}

/// The accumulator threaded to the next step proof
/// (`Messages_for_next_step_proof`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MessagesForNextStepProof<Comm, S, Comms, BpChals> {
    /// The application-level state.
    pub app_state: S,
    /// The wrap-circuit verification key.
    pub dlog_plonk_index: PlonkVerificationKeyEvals<Comm>,
    /// The previous challenge-polynomial commitments.
    pub challenge_polynomial_commitments: Comms,
    /// The previous bulletproof challenges.
    pub old_bulletproof_challenges: BpChals,
}

impl<Comm, S, F: Clone> MessagesForNextStepProof<Comm, S, Vec<Comm>, Vec<Vec<F>>> {
    /// `Messages_for_next_step_proof.to_field_elements`: verification key
    /// commitments first, then app state, then each challenge-polynomial
    /// commitment followed by its bulletproof challenges.
    pub fn to_field_elements(
        &self,
        app_state_to_field_elements: impl Fn(&S) -> Vec<F>,
        index_comm_to_field_elements: impl Fn(&Comm) -> Vec<F>,
        comm_to_field_elements: impl Fn(&Comm) -> Vec<F>,
    ) -> Vec<F> {
        let mut out = Vec::new();
        for comm in self.dlog_plonk_index.to_list() {
            out.extend(index_comm_to_field_elements(comm));
        }
        out.extend(
            self.to_field_elements_without_index(
                app_state_to_field_elements,
                comm_to_field_elements,
            ),
        );
        out
    }

    /// `Messages_for_next_step_proof.to_field_elements_without_index`.
    pub fn to_field_elements_without_index(
        &self,
        app_state_to_field_elements: impl Fn(&S) -> Vec<F>,
        comm_to_field_elements: impl Fn(&Comm) -> Vec<F>,
    ) -> Vec<F> {
        assert_eq!(
            self.challenge_polynomial_commitments.len(),
            self.old_bulletproof_challenges.len(),
            "MessagesForNextStepProof: one challenge vector per commitment"
        );
        let mut out = app_state_to_field_elements(&self.app_state);
        for (comm, chals) in self
            .challenge_polynomial_commitments
            .iter()
            .zip(&self.old_bulletproof_challenges)
        {
            out.extend(comm_to_field_elements(comm));
            out.extend(chals.iter().cloned());
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar_challenge::ScalarChallenge;
    use mina_curves::pasta::Fq;

    type Chal = Fq;
    type WrapDeferredValues = DeferredValues<
        plonk::Minimal<Chal, ScalarChallenge<Chal>, bool>,
        Fq,
        ScalarChallenge<Chal>,
        Vec<BulletproofChallenge<ScalarChallenge<Chal>>>,
        (),
    >;

    #[test]
    fn construct_wrap_deferred_values() {
        // sanity: the generic instantiation used by the step verifier
        let dv: WrapDeferredValues = DeferredValues {
            plonk: plonk::Minimal {
                alpha: ScalarChallenge(Fq::from(1u64)),
                beta: Fq::from(2u64),
                gamma: Fq::from(3u64),
                zeta: ScalarChallenge(Fq::from(4u64)),
                joint_combiner: None,
                feature_flags: Features::none(),
            },
            combined_inner_product: Fq::from(5u64),
            b: Fq::from(6u64),
            xi: ScalarChallenge(Fq::from(7u64)),
            bulletproof_challenges: (0..crate::common::TOCK_ROUNDS)
                .map(|i| BulletproofChallenge {
                    prechallenge: ScalarChallenge(Fq::from(i as u64)),
                })
                .collect(),
            branch_data: (),
        };
        assert_eq!(dv.bulletproof_challenges.len(), crate::common::TOCK_ROUNDS);
        assert_eq!(dv.plonk.feature_flags, Features::none());
    }

    #[test]
    fn proof_slots_are_front_padded_to_width_two() {
        assert_eq!(ProofsVerified::N0.prefix_mask(), [false, false]);
        assert_eq!(ProofsVerified::N1.prefix_mask(), [false, true]);
        assert_eq!(ProofsVerified::N2.prefix_mask(), [true, true]);
        assert_eq!(
            front_pad_proof_slots(vec![7u64]),
            [ProofSlot::Dummy, ProofSlot::Proof(7)]
        );
        assert_eq!(
            front_pad_proof_slots(vec![7u64, 8]),
            [ProofSlot::Proof(7), ProofSlot::Proof(8)]
        );
    }

    #[test]
    fn features_to_data_order_round_trips() {
        let features = Features {
            range_check0: true,
            range_check1: false,
            foreign_field_add: true,
            foreign_field_mul: false,
            xor: true,
            rot: false,
            lookup: true,
            runtime_tables: false,
        };
        assert_eq!(
            features.to_data(),
            [true, false, true, false, true, false, true, false]
        );
        assert_eq!(Features::from_data(features.to_data()), features);
    }

    #[test]
    fn messages_for_next_wrap_to_field_elements() {
        // commitment represented by its two coordinates
        let msg = wrap::MessagesForNextWrapProof {
            challenge_polynomial_commitment: (Fq::from(10u64), Fq::from(11u64)),
            old_bulletproof_challenges: vec![
                vec![Fq::from(1u64), Fq::from(2u64)],
                vec![Fq::from(3u64), Fq::from(4u64)],
            ],
        };
        let fe = msg.to_field_elements(|(x, y)| vec![*x, *y]);
        // flattened challenges first, then the commitment coordinates
        assert_eq!(
            fe,
            vec![
                Fq::from(1u64),
                Fq::from(2u64),
                Fq::from(3u64),
                Fq::from(4u64),
                Fq::from(10u64),
                Fq::from(11u64),
            ]
        );
    }

    #[test]
    fn messages_for_next_step_to_field_elements_order() {
        let comm = |i| (Fq::from(i), Fq::from(100 + i));
        let msg = MessagesForNextStepProof {
            app_state: vec![Fq::from(1u64), Fq::from(2u64)],
            dlog_plonk_index: PlonkVerificationKeyEvals {
                sigma_comm: (10..17).map(comm).collect(),
                coefficients_comm: (20..35).map(comm).collect(),
                generic_comm: comm(40),
                psm_comm: comm(41),
                complete_add_comm: comm(42),
                mul_comm: comm(43),
                emul_comm: comm(44),
                endomul_scalar_comm: comm(45),
            },
            challenge_polynomial_commitments: vec![comm(50), comm(51)],
            old_bulletproof_challenges: vec![
                vec![Fq::from(3u64), Fq::from(4u64)],
                vec![Fq::from(5u64), Fq::from(6u64)],
            ],
        };
        let app = |xs: &Vec<Fq>| xs.clone();
        let point = |(x, y): &(Fq, Fq)| vec![*x, *y];

        let without = msg.to_field_elements_without_index(app, point);
        assert_eq!(
            without,
            vec![
                Fq::from(1u64),
                Fq::from(2u64),
                Fq::from(50u64),
                Fq::from(150u64),
                Fq::from(3u64),
                Fq::from(4u64),
                Fq::from(51u64),
                Fq::from(151u64),
                Fq::from(5u64),
                Fq::from(6u64),
            ]
        );

        let with = msg.to_field_elements(app, point, point);
        let index_len = (7 + 15 + 6) * 2;
        assert_eq!(&with[index_len..], without.as_slice());
        assert_eq!(
            &with[..4],
            &[
                Fq::from(10u64),
                Fq::from(110u64),
                Fq::from(11u64),
                Fq::from(111u64)
            ]
        );
    }

    #[test]
    fn branch_data_pack_unpack_round_trips() {
        for proofs_verified in [ProofsVerified::N0, ProofsVerified::N1, ProofsVerified::N2] {
            let branch = BranchData {
                proofs_verified,
                domain_log2: 15,
            };
            assert_eq!(BranchData::unpack(branch.pack::<Fq>()), branch);
        }
    }

    #[test]
    #[should_panic(expected = "ProofsVerified: expected 0, 1 or 2")]
    fn branch_data_unpack_rejects_proofs_verified_3() {
        let _ = BranchData::unpack::<Fq>(Fq::from(3u64));
    }

    #[test]
    fn wrap_statement_to_field_elements_order() {
        let plonk = plonk::InCircuit {
            alpha: ScalarChallenge(Fq::from(107u64)),
            beta: Fq::from(105u64),
            gamma: Fq::from(106u64),
            zeta: ScalarChallenge(Fq::from(108u64)),
            zeta_to_srs_length: Fq::from(102u64),
            zeta_to_domain_size: Fq::from(103u64),
            perm: Fq::from(104u64),
            feature_flags: Features::none(),
            joint_combiner: None,
        };
        let bp: Vec<BulletproofChallenge<ScalarChallenge<Fq>>> = (0..16)
            .map(|i| BulletproofChallenge {
                prechallenge: ScalarChallenge(Fq::from(200u64 + i as u64)),
            })
            .collect();
        let branch = BranchData {
            proofs_verified: ProofsVerified::N2,
            domain_log2: 15,
        };
        let fe = wrap::wrap_statement_to_field_elements(
            &plonk,
            Fq::from(100u64),                   // combined_inner_product
            Fq::from(101u64),                   // b
            &ScalarChallenge(Fq::from(109u64)), // xi
            &bp,
            &branch,
            Fq::from(110u64), // sponge digest
            Fq::from(111u64), // messages_for_next_wrap digest
            Fq::from(112u64), // messages_for_next_step digest
        );

        let mut expected: Vec<Fq> = vec![
            100, 101, 102, 103, 104, // fp
            105, 106, // challenge
            107, 108, 109, // scalar_challenge
            110, 111, 112, // digest
        ]
        .into_iter()
        .map(Fq::from)
        .collect();
        expected.extend((200..216).map(Fq::from)); // bulletproof_challenges
        expected.push(Fq::from(15u64 * 4 + 2)); // branch_data pack
        expected.extend(std::iter::repeat_n(Fq::from(0u64), 8)); // feature_flags
        assert_eq!(fe, expected);
        assert_eq!(fe.len(), 5 + 2 + 3 + 3 + 16 + 1 + 8);
    }

    #[test]
    fn step_statement_to_field_elements_order() {
        let plonk = plonk::InCircuit {
            alpha: ScalarChallenge(Fq::from(108u64)),
            beta: Fq::from(106u64),
            gamma: Fq::from(107u64),
            zeta: ScalarChallenge(Fq::from(109u64)),
            zeta_to_srs_length: Fq::from(102u64),
            zeta_to_domain_size: Fq::from(103u64),
            perm: Fq::from(104u64),
            feature_flags: Features::none(),
            joint_combiner: None,
        };
        let bp: Vec<BulletproofChallenge<ScalarChallenge<Fq>>> = (0..crate::common::TOCK_ROUNDS)
            .map(|i| BulletproofChallenge {
                prechallenge: ScalarChallenge(Fq::from(200u64 + i as u64)),
            })
            .collect();
        let unfinalized = step::unfinalized_to_field_elements(
            &plonk,
            Fq::from(100u64),                   // combined_inner_product
            Fq::from(101u64),                   // b
            &ScalarChallenge(Fq::from(110u64)), // xi
            &bp,
            Fq::from(105u64), // sponge digest
            true,             // should_finalize
        );

        // fq[5], digest[1] (before the challenges — unlike wrap),
        // challenge[2], scalar_challenge[3], bp[15], bool[1]
        let mut expected: Vec<Fq> = vec![
            100, 101, 102, 103, 104, // fq
            105, // digest
            106, 107, // challenge
            108, 109, 110, // scalar_challenge
        ]
        .into_iter()
        .map(Fq::from)
        .collect();
        expected.extend((200..200 + crate::common::TOCK_ROUNDS as u64).map(Fq::from));
        expected.push(Fq::from(1u64)); // should_finalize
        assert_eq!(unfinalized, expected);
        assert_eq!(
            unfinalized.len(),
            5 + 1 + 2 + 3 + crate::common::TOCK_ROUNDS + 1
        );

        // statement = unfinalized[N] ++ msgs_next_step ++ msgs_next_wrap[N]
        let stmt = step::step_statement_to_field_elements(
            &[unfinalized.clone(), unfinalized.clone()],
            Fq::from(300u64),
            &[Fq::from(301u64), Fq::from(302u64)],
        );
        assert_eq!(stmt.len(), 2 * unfinalized.len() + 1 + 2);
        assert_eq!(stmt[2 * unfinalized.len()], Fq::from(300u64));
        assert_eq!(*stmt.last().unwrap(), Fq::from(302u64));
    }

    #[test]
    fn vk_evals_to_list_order() {
        use kimchi::circuits::wires::{COLUMNS, PERMUTS};
        let vk = PlonkVerificationKeyEvals {
            sigma_comm: (0..PERMUTS).map(|i| i as u32).collect(),
            coefficients_comm: (0..COLUMNS).map(|i| 100 + i as u32).collect(),
            generic_comm: 200,
            psm_comm: 201,
            complete_add_comm: 202,
            mul_comm: 203,
            emul_comm: 204,
            endomul_scalar_comm: 205,
        };
        let list: Vec<u32> = vk.to_list().into_iter().copied().collect();
        assert_eq!(list.len(), PERMUTS + COLUMNS + 6);
        assert_eq!(list[0], 0); // first sigma
        assert_eq!(list[PERMUTS], 100); // first coefficient
        assert_eq!(list[PERMUTS + COLUMNS], 200); // generic
        assert_eq!(*list.last().unwrap(), 205); // endomul_scalar
    }
}
