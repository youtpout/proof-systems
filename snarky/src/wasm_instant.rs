//! A wall-clock instant that works on `wasm32`, where
//! `std::time::Instant::now()` panics ("time not implemented on this
//! platform"). Such a panic inside a rayon pool worker leaves the main thread
//! parked forever on the `install` latch — a silent deadlock in the wasm
//! bindings — so every profiling timestamp in the proving path must go through
//! this shim instead of `std::time::Instant`.
//!
//! On wasm32 the clock is `js_sys::Date::now()` (millisecond wall time,
//! available on the main thread and in pool workers alike); on every other
//! target it is a plain `std::time::Instant`.

use std::time::Duration;

/// Drop-in replacement for `std::time::Instant` restricted to the operations
/// the profiling code uses (`now`, `elapsed`, `Sub`).
#[derive(Clone, Copy, Debug)]
pub struct Instant {
    #[cfg(not(target_arch = "wasm32"))]
    inner: std::time::Instant,
    #[cfg(target_arch = "wasm32")]
    ms: f64,
}

impl Instant {
    pub fn now() -> Self {
        #[cfg(not(target_arch = "wasm32"))]
        {
            Instant {
                inner: std::time::Instant::now(),
            }
        }
        #[cfg(target_arch = "wasm32")]
        {
            Instant {
                ms: js_sys::Date::now(),
            }
        }
    }

    pub fn elapsed(&self) -> Duration {
        Instant::now() - *self
    }
}

impl std::ops::Sub for Instant {
    type Output = Duration;

    fn sub(self, earlier: Instant) -> Duration {
        #[cfg(not(target_arch = "wasm32"))]
        {
            self.inner.saturating_duration_since(earlier.inner)
        }
        #[cfg(target_arch = "wasm32")]
        {
            Duration::from_secs_f64((self.ms - earlier.ms).max(0.0) / 1000.0)
        }
    }
}
