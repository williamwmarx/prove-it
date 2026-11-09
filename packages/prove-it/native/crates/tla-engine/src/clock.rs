//! The clock the search times its progress reports and liveness checks by. WebAssembly has no
//! clock of its own, so there the host gives the time.

#[cfg(not(target_arch = "wasm32"))]
pub use std::time::Instant;

#[cfg(target_arch = "wasm32")]
pub use host::Instant;

#[cfg(target_arch = "wasm32")]
mod host {
    use std::ops::{Add, Sub};
    use std::time::Duration;

    #[link(wasm_import_module = "env")]
    unsafe extern "C" {
        /// The host's monotonic time in milliseconds, as `performance.now()` gives it.
        fn prove_it_now() -> f64;
    }

    /// A moment of the host's clock, in milliseconds.
    #[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
    pub struct Instant(f64);

    impl Instant {
        pub fn now() -> Instant {
            Instant(unsafe { prove_it_now() })
        }

        pub fn elapsed(&self) -> Duration {
            Instant::now() - *self
        }
    }

    impl Add<Duration> for Instant {
        type Output = Instant;

        fn add(self, duration: Duration) -> Instant {
            Instant(self.0 + duration.as_secs_f64() * 1000.0)
        }
    }

    impl Sub for Instant {
        type Output = Duration;

        fn sub(self, earlier: Instant) -> Duration {
            Duration::from_secs_f64((self.0 - earlier.0).max(0.0) / 1000.0)
        }
    }
}
