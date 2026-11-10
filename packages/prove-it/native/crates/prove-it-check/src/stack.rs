//! Where the check runs what recurses deeply: the search, and the evaluator that rebuilds traces,
//! failures and the startup. Each runs on a thread with the search's stack. WebAssembly has no
//! threads, so there each runs in place, on the stack the module links.

#[cfg(not(target_arch = "wasm32"))]
use std::panic::resume_unwind;

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
    std::thread::scope(|scope| {
        let working = std::thread::Builder::new()
            .stack_size(SEARCH_STACK_BYTES)
            .spawn_scoped(scope, work)
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
    std::thread::scope(|scope| {
        let map = &map;
        let mapping: Vec<_> = items.map(|item| scope.spawn(move || map(item))).collect();
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
