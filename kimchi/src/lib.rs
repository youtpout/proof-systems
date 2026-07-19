#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]
// Allow non_local_definitions from derive macros (proptest_derive, ocaml)
// until upstream crates are updated.
// See https://github.com/o1-labs/mina-rust/issues/1954
#![allow(non_local_definitions)]

extern crate alloc;

// Re-export alloc types so all modules have access in no_std mode.
// This is used instead of patching every file individually.
#[allow(unused_imports)]
#[doc(hidden)]
mod prelude {
    pub use alloc::{
        borrow::ToOwned,
        boxed::Box,
        format,
        string::{String, ToString},
        vec,
        vec::Vec,
    };
}

// Pull prelude into scope for all modules in this crate.
#[allow(unused_imports)]
use prelude::*;

pub use poly_commitment::collections;

pub use groupmap;
pub use mina_curves;
pub use mina_poseidon;
pub use o1_utils;
pub use poly_commitment;

pub mod alphas;
#[cfg(feature = "prover")]
pub mod bench;
pub mod circuits;
pub mod curve;
pub mod error;
#[cfg(feature = "prover")]
pub mod lagrange_basis_evaluations;
pub mod linearization;
pub mod oracles;
pub mod plonk_sponge;
pub mod proof;
#[cfg(feature = "prover")]
pub mod prover;
#[cfg(feature = "prover")]
pub mod prover_index;
pub mod verifier;
pub mod verifier_index;

#[cfg(test)]
mod tests;

/// Handy macro to return the filename and line number of a place in the code.
#[macro_export]
macro_rules! loc {
    () => {{
        ::alloc::borrow::Cow::Owned(format!("{}:{}", file!(), line!()))
    }};
}

/// Minimal live checkpoint hook: wasm has no stderr and a hung pool never
/// returns, so hosts (kimchi-wasm) can install a console-backed hook to see
/// prover phases in real time. No-op unless a hook is installed.
pub mod live_trace {
    static HOOK: std::sync::Mutex<Option<fn(&str)>> = std::sync::Mutex::new(None);
    /// Recorded checkpoints, readable from another thread over the shared
    /// wasm memory while the main thread is blocked inside a call.
    static RECORD: std::sync::Mutex<Vec<String>> = std::sync::Mutex::new(Vec::new());

    /// Host-installed wall clock in milliseconds (js Date.now on wasm).
    /// While installed, the time between two consecutive checkpoints is
    /// accumulated under the FIRST one's name — phase profiling for free
    /// from the existing checkpoint markers. A name ending in `_done`
    /// closes the last interval without opening one.
    static CLOCK: std::sync::Mutex<Option<fn() -> f64>> = std::sync::Mutex::new(None);
    static LAST_MARK: std::sync::Mutex<Option<(String, f64)>> = std::sync::Mutex::new(None);
    static PHASE_MS: std::sync::Mutex<Vec<(String, f64, u32)>> = std::sync::Mutex::new(Vec::new());

    pub fn set_hook(hook: fn(&str)) {
        *HOOK.lock().unwrap() = Some(hook);
    }

    pub fn set_clock(clock: fn() -> f64) {
        *CLOCK.lock().unwrap() = Some(clock);
    }

    /// Drains the accumulated per-phase wall times: (phase, total ms, count).
    pub fn take_phase_times() -> Vec<(String, f64, u32)> {
        PHASE_MS
            .lock()
            .map(|mut v| std::mem::take(&mut *v))
            .unwrap_or_default()
    }

    fn mark_phase(name: &str) {
        let now = match CLOCK.lock().ok().and_then(|c| *c) {
            Some(clock) => clock(),
            None => return,
        };
        let closing = name.ends_with("_done");
        let prev = match LAST_MARK.lock() {
            Ok(mut last) => last.replace((name.to_string(), now)).map(|(n, t)| {
                if closing {
                    *last = None;
                }
                (n, now - t)
            }),
            Err(_) => return,
        };
        if let (Some((prev_name, dt)), Ok(mut acc)) = (prev, PHASE_MS.lock()) {
            match acc.iter_mut().find(|(n, _, _)| *n == prev_name) {
                Some((_, total, count)) => {
                    *total += dt;
                    *count += 1;
                },
                None => acc.push((prev_name, dt, 1)),
            }
        }
    }

    pub fn checkpoint(name: &str) {
        mark_phase(name);
        if let Ok(mut record) = RECORD.lock() {
            record.push(name.to_string());
            if record.len() > 512 {
                record.remove(0);
            }
        }
        if let Ok(hook) = HOOK.lock() {
            if let Some(hook) = *hook {
                hook(name);
            }
        }
    }

    /// Drains the recorded checkpoints (tracer-thread polling).
    pub fn take_recorded() -> Vec<String> {
        RECORD
            .lock()
            .map(|mut record| std::mem::take(&mut *record))
            .unwrap_or_default()
    }
}
