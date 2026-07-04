//! Common constants and helpers (port of pickles' `common.ml`).

/// The maximum number of previous proofs a step circuit can verify.
/// (OCaml: `Nat.N2` — pickles is specialized to width 2.)
pub const MAX_PROOFS_VERIFIED: usize = 2;

/// The number of bits used for scalar challenges.
/// (OCaml: `Challenge.Constant.length = 128`.)
pub const SCALAR_CHALLENGE_BITS: usize = 128;

/// The number of rounds of the IPA on the Tick (step / Vesta) side —
/// log2 of the maximum domain size.
pub const TICK_ROUNDS: usize = 16;

/// The number of rounds of the IPA on the Tock (wrap / Pallas) side.
pub const TOCK_ROUNDS: usize = 15;

/// The Poseidon full-rounds constant shared with the snarky crate.
pub const FULL_ROUNDS: usize = snarky::FULL_ROUNDS;
