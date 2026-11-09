//! Prove It's native engine, loaded by `src/engine/native.ts` as an N-API addon. `prove-it-host`
//! searches the model and builds what the addon hands JavaScript; the binding marshals it.

#[cfg(not(test))]
mod binding;

pub use prove_it_host::*;
