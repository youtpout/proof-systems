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
pub mod api;
pub mod bulletproof;
pub mod challenge;
pub mod commitments;
pub mod common;
pub mod composition_types;
pub mod dummy;
pub mod endo;
pub mod expr_eval;
pub mod scalars_ml;
pub mod finalize;
pub mod fr_sponge;
pub mod ft_eval_circuit;
pub mod hash_messages;
pub mod incrementally_verify;
pub mod inductive_rule;
pub mod ipa;
pub mod mina_bin_prot;
pub mod mina_sexp;
pub mod opt_sponge;
pub mod oracles;
pub mod plonk_checks;
pub mod plonk_curve_ops;
pub mod public_input;
pub mod recorded;
pub mod template_dummy;
pub mod recursive_step;
pub mod reduced_messages;
pub mod ro;
pub mod scalar_challenge;
pub mod shifted_value;
pub mod side_loaded;
pub mod sponge;
pub mod step_main;
pub mod step_verifier;
pub mod step_witness;
pub mod verify;
pub mod wrap;
pub mod wrap_deferred_values;
pub mod wrap_main;

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

/// Coarse per-stage timings of the cache-restore paths. Recording is a no-op
/// until a hook is installed, so the instrumentation is free in production; the
/// wasm layer installs a hook that logs the breakdown to the console.
pub mod restore_profile {
    static HOOK: std::sync::Mutex<Option<fn(&str, u64)>> = std::sync::Mutex::new(None);

    pub fn set_restore_stage_hook(hook: Option<fn(&str, u64)>) {
        *HOOK.lock().unwrap() = hook;
    }

    pub fn stages_enabled() -> bool {
        HOOK.lock().unwrap().is_some()
    }

    fn record_stage(name: &str, micros: u64) {
        let hook = *HOOK.lock().unwrap();
        if let Some(hook) = hook {
            hook(name, micros);
        }
    }

    /// Times `body` and reports it under `name`.
    pub fn stage<T>(name: &str, body: impl FnOnce() -> T) -> T {
        if !stages_enabled() {
            return body();
        }
        let started = snarky::wasm_instant::Instant::now();
        let out = body();
        record_stage(
            name,
            (snarky::wasm_instant::Instant::now() - started).as_micros() as u64,
        );
        out
    }
}

pub use snarky::api::{set_compile_profile_hook, CompileProfile};
/// A clock that works on both native and wasm targets, for the profiling hooks.
pub use snarky::wasm_instant;
pub use tick_tock::{Side, Tick, Tock};
