//! A wall-clock instant that degrades to a no-op on `wasm32-unknown-unknown`,
//! where `std::time::Instant::now()` panics ("time not implemented on this
//! platform"). Such a panic inside a rayon pool worker leaves the main thread
//! parked forever on the `install` latch — a silent deadlock in the wasm
//! bindings — so every profiling timestamp in the proving path must go through
//! this shim instead of `std::time::Instant`.

use std::time::Duration;

/// Drop-in replacement for `std::time::Instant` restricted to the operations
/// the profiling code uses (`now`, `elapsed`, `Sub`). On wasm32 every duration
/// reads as zero.
#[derive(Clone, Copy, Debug)]
pub struct Instant(#[cfg(not(target_arch = "wasm32"))] std::time::Instant);

impl Instant {
    pub fn now() -> Self {
        #[cfg(not(target_arch = "wasm32"))]
        {
            Instant(std::time::Instant::now())
        }
        #[cfg(target_arch = "wasm32")]
        {
            Instant()
        }
    }

    pub fn elapsed(&self) -> Duration {
        #[cfg(not(target_arch = "wasm32"))]
        {
            self.0.elapsed()
        }
        #[cfg(target_arch = "wasm32")]
        {
            Duration::ZERO
        }
    }
}

impl std::ops::Sub for Instant {
    type Output = Duration;

    fn sub(self, earlier: Instant) -> Duration {
        #[cfg(not(target_arch = "wasm32"))]
        {
            self.0 - earlier.0
        }
        #[cfg(target_arch = "wasm32")]
        {
            let _ = earlier;
            Duration::ZERO
        }
    }
}
