//! Where the check runs what recurses deeply: the search, and the evaluator that rebuilds traces,
//! failures and the startup. Each runs on a thread with the search's stack. WebAssembly has no
//! threads, so there each runs in place, on the stack the module links.

#[cfg(not(target_arch = "wasm32"))]
use std::panic::resume_unwind;

/// The stack of the thread a check runs on, in the binary and in the native addon: the front end
/// recurses as deep as TLC's translation of a formula does before it reports TLC's stack overflow,
/// 2,000 calls of a recursive operator, which a main thread's stack, 1 MiB on Windows, doesn't
/// hold. It is reserved, not committed.
pub const RUN_STACK_BYTES: usize = 256 * 1024 * 1024;

/// How deep the search's thread's stack may grow: the evaluator recurses with the expressions and
/// the values it evaluates. It is reserved, not committed.
#[cfg(not(target_arch = "wasm32"))]
const SEARCH_STACK_BYTES: usize = 256 * 1024 * 1024;

/// Runs `work` with the search's stack.
pub fn on_search_stack<T: Send>(work: impl FnOnce() -> T + Send) -> T {
    alongside(work, || {})
}

/// Runs `work` with the search's stack while `consume` runs on this thread, and returns what
/// `work` returns. In WebAssembly, `work` runs first and `consume` after it.
#[cfg(not(target_arch = "wasm32"))]
pub fn alongside<T: Send>(work: impl FnOnce() -> T + Send, consume: impl FnOnce()) -> T {
    // The thread writes files for the check this one runs ([`tla_values::written`]).
    let journal = tla_values::written::current();
    std::thread::scope(|scope| {
        let working = std::thread::Builder::new()
            .stack_size(SEARCH_STACK_BYTES)
            .spawn_scoped(scope, move || {
                tla_values::written::enter(journal.as_ref(), work)
            })
            .expect("a thread with the search's stack");
        consume();
        working.join().unwrap_or_else(|panic| resume_unwind(panic))
    })
}

#[cfg(target_arch = "wasm32")]
pub fn alongside<T: Send>(work: impl FnOnce() -> T + Send, consume: impl FnOnce()) -> T {
    let result = work();
    consume();
    result
}

/// `map` of each item, on a thread of its own where there are threads.
#[cfg(not(target_arch = "wasm32"))]
pub fn map_on_threads<T: Send, U: Send>(
    items: impl Iterator<Item = T>,
    map: impl Fn(T) -> U + Sync,
) -> Vec<U> {
    let journal = tla_values::written::current();
    std::thread::scope(|scope| {
        let (map, journal) = (&map, &journal);
        let mapping: Vec<_> = items
            .map(|item| {
                scope.spawn(move || tla_values::written::enter(journal.as_ref(), || map(item)))
            })
            .collect();
        mapping
            .into_iter()
            .map(|thread| thread.join().unwrap_or_else(|panic| resume_unwind(panic)))
            .collect()
    })
}

#[cfg(target_arch = "wasm32")]
pub fn map_on_threads<T: Send, U: Send>(
    items: impl Iterator<Item = T>,
    map: impl Fn(T) -> U + Sync,
) -> Vec<U> {
    items.map(map).collect()
}
