//! Rust port of Mina's **Pickles** recursive proof system.
//!
//! Pickles composes kimchi proofs recursively over the Pasta cycle:
//! - **step** proofs live on the *Tick* side (circuits over Fp, proved with
//!   Vesta/IPA), and verify *wrap* proofs;
//! - **wrap** proofs live on the *Tock* side (circuits over Fq, proved with
//!   Pallas/IPA), and verify *step* proofs.
//!
//! The OCaml reference lives in mina's `src/lib/crypto/pickles` (49 modules);
//! this crate is being ported module by module on top of the [snarky] crate
//! (the DSL and constraint system, already at gate parity with the OCaml).
//! See `pickles/CLAUDE.md` for the port map and status.

pub mod all_evals;
pub mod challenge;
pub mod common;
pub mod composition_types;
pub mod endo;
pub mod expr_eval;
pub mod finalize;
pub mod fr_sponge;
pub mod ft_eval_circuit;
pub mod ipa;
pub mod opt_sponge;
pub mod oracles;
pub mod plonk_checks;
pub mod plonk_curve_ops;
pub mod scalar_challenge;
pub mod sponge;

/// The two sides of the Pasta recursion cycle.
pub mod tick_tock {
    use mina_curves::pasta::{Fp, Fq, Pallas, Vesta};

    /// The *Tick* side: step circuits over [Fp], proved on [Vesta].
    pub struct Tick;

    /// The *Tock* side: wrap circuits over [Fq], proved on [Pallas].
    pub struct Tock;

    /// Field, curve and proof types of one side of the cycle.
    pub trait Side {
        /// The circuit (scalar) field.
        type Field: ark_ff::PrimeField;
        /// The curve the proofs are made on.
        type Curve;
        /// The other side's curve (whose points have coordinates in
        /// [Self::Field]).
        type OtherCurve;
    }

    impl Side for Tick {
        type Field = Fp;
        type Curve = Vesta;
        type OtherCurve = Pallas;
    }

    impl Side for Tock {
        type Field = Fq;
        type Curve = Pallas;
        type OtherCurve = Vesta;
    }
}

pub use tick_tock::{Side, Tick, Tock};
