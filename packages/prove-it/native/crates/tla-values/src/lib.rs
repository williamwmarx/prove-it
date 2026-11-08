//! The values of Prove It's native engine: a hash-consed store of TLA+ values that hands out the
//! same ids as `src/engine/store.ts` for the same operations, TLC's order and the places where TLC
//! fails to compare, TLC's FP64 fingerprints of values and states, and `src/transfer.ts`'s
//! encoding of states.

pub mod fingerprint;
pub mod store;
pub mod trace;
pub mod transfer;

pub use store::{Bail, Id, Store};
