//! Common constants and helpers (port of pickles' `common.ml`).

use crate::composition_types::ProofsVerified;
use mina_curves::pasta::{Pallas, Vesta};
use poly_commitment::{ipa::SRS, SRS as _};
use std::sync::{Arc, OnceLock};

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

/// Returns Mina's full Tick SRS.
///
/// `SnarkyCircuit` passes the circuit domain size here. That domain can be
/// smaller than Mina's fixed proof SRS (for example the 512-row base Step
/// circuit), so it must not be used as the SRS size or asserted to equal it.
pub(crate) fn tick_srs(_domain_size: usize) -> Arc<SRS<Vesta>> {
    static TICK_SRS: OnceLock<Arc<SRS<Vesta>>> = OnceLock::new();
    TICK_SRS
        .get_or_init(|| Arc::new(SRS::<Vesta>::create(1 << TICK_ROUNDS)))
        .clone()
}

/// Returns Mina's full Tock SRS independently of the circuit domain size.
pub(crate) fn tock_srs(_domain_size: usize) -> Arc<SRS<Pallas>> {
    static TOCK_SRS: OnceLock<Arc<SRS<Pallas>>> = OnceLock::new();
    TOCK_SRS
        .get_or_init(|| Arc::new(SRS::<Pallas>::create(1 << TOCK_ROUNDS)))
        .clone()
}

/// The Poseidon full-rounds constant shared with the snarky crate.
pub const FULL_ROUNDS: usize = snarky::FULL_ROUNDS;

/// The default number of commitment chunks (`Plonk_checks.num_chunks_by_default`);
/// the base step/wrap circuits use a single chunk per column.
pub const NUM_CHUNKS_BY_DEFAULT: usize = 1;

/// The log2 domain size of the wrap circuit as a function of the number of
/// proofs it verifies (`Common.wrap_domains`): `0 -> 13`, `1 -> 14`, `2 -> 15`.
///
/// # Panics
/// Panics if `proofs_verified > 2` (pickles is specialized to width ≤ 2).
pub fn wrap_domain_log2(proofs_verified: usize) -> u32 {
    match proofs_verified {
        0 => 13,
        1 => 14,
        2 => 15,
        _ => panic!("wrap_domain_log2: proofs_verified must be 0, 1 or 2"),
    }
}

/// Inverse of [`wrap_domain_log2`] (`Common.actual_wrap_domain_size`): recovers
/// the number of proofs verified by a padded wrap circuit domain.
///
/// # Panics
/// Panics if `log2_domain_size` is not one of 13, 14 or 15.
pub fn actual_wrap_domain_size(log2_domain_size: u32) -> ProofsVerified {
    match log2_domain_size {
        13 => ProofsVerified::N0,
        14 => ProofsVerified::N1,
        15 => ProofsVerified::N2,
        _ => panic!("actual_wrap_domain_size: log2 domain size must be 13, 14 or 15"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `wrap_domain_log2` reproduces `Common.wrap_domains` (common.ml).
    #[test]
    fn wrap_domain_log2_matches_ocaml() {
        assert_eq!(wrap_domain_log2(0), 13);
        assert_eq!(wrap_domain_log2(1), 14);
        assert_eq!(wrap_domain_log2(2), 15);
    }

    #[test]
    #[should_panic(expected = "proofs_verified must be 0, 1 or 2")]
    fn wrap_domain_log2_rejects_width_3() {
        let _ = wrap_domain_log2(3);
    }

    /// `actual_wrap_domain_size` reproduces `Common.actual_wrap_domain_size`.
    #[test]
    fn actual_wrap_domain_size_matches_ocaml() {
        assert_eq!(actual_wrap_domain_size(13), ProofsVerified::N0);
        assert_eq!(actual_wrap_domain_size(14), ProofsVerified::N1);
        assert_eq!(actual_wrap_domain_size(15), ProofsVerified::N2);
    }

    #[test]
    #[should_panic(expected = "log2 domain size must be 13, 14 or 15")]
    fn actual_wrap_domain_size_rejects_other_domains() {
        let _ = actual_wrap_domain_size(12);
    }
}
