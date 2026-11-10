//! The values of Prove It's native engine: a hash-consed store of TLA+ values that hands out the
//! same ids as `src/engine/store.ts` for the same operations, TLC's order and the places where TLC
//! fails to compare, TLC's FP64 fingerprints of values and states, TLC's text of values, and
//! `src/transfer.ts`'s encoding of states.

pub mod fingerprint;
pub mod json;
pub mod print;
pub mod random;
pub mod store;
pub mod trace;
pub mod transfer;

pub use store::{Bail, Id, Store};

/// The stack the store's callers run it on. `compare`, `equals` and the transfer encoding follow
/// nested values by recursion, and a Rust stack overflow aborts the process rather than failing,
/// so they run on a thread whose stack holds values nested 100,000 deep, past where the TypeScript
/// store runs out of stack (between 10,000 and 30,000 in Bun). The stack is reserved, not
/// committed.
pub const NESTING_STACK_BYTES: usize = if cfg!(debug_assertions) {
    1024 * 1024 * 1024
} else {
    256 * 1024 * 1024
};

/// Runs work on a thread with a stack for deeply nested values, and returns what it returns.
pub fn on_nesting_stack<T: Send>(work: impl FnOnce() -> T + Send) -> T {
    // WebAssembly runs on one thread, whose stack the module sets as it links.
    #[cfg(target_arch = "wasm32")]
    return work();
    #[cfg(not(target_arch = "wasm32"))]
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(NESTING_STACK_BYTES)
            .spawn_scoped(scope, work)
            .expect("a thread for nested values")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}
