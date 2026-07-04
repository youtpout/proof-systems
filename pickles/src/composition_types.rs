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

/// Data identifying which step branch was verified (`branch_data.ml`).
/// `domain_log2` is the log2 of the step circuit's domain size.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BranchData {
    pub proofs_verified: ProofsVerified,
    pub domain_log2: u8,
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
    use super::DeferredValues;

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
}
