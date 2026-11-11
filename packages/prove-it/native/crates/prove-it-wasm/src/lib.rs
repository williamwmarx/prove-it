//! Prove It's native engine as a WebAssembly module, which `src/engine/wasm.ts` instantiates where
//! there is no `process.dlopen`, as in a browser. It offers what the N-API addon does, through a
//! hand-written ABI over the module's memory: the loader writes each call's arguments as one
//! array in `encoding`'s format, and reads back the result in it.
//!
//! - `prove_it_alloc(length)` and `prove_it_free(pointer, length)` manage buffers in the memory;
//! - `prove_it_abi_version()` is the addon's `abiVersion()`;
//! - `prove_it_check`, `prove_it_sany_text`, `prove_it_sany_xml`, `prove_it_check_sources`,
//!   `prove_it_store_perform`, `prove_it_store_decode`, `prove_it_store_encode`,
//!   `prove_it_store_fingerprints` and `prove_it_store_reset_fingerprints` each take the buffer
//!   of their arguments, which they free, and return a buffer of a u32 length, a status byte, 0
//!   for a result or 1 for the message of a TypeError, and the value.
//!   Where the addon writes into an array it is given, the hook returns the new elements instead.
//!
//! The module imports `prove_it_now()`, the host's clock in milliseconds, and, while `check` runs,
//! `prove_it_report(kind, a, b, c, d, e, f)` and `prove_it_print(pointer, length)`, the latter with
//! `[width, words, strings]` encoded, and `prove_it_write(path, pathLength, bytes, length,
//! isAppended)` for the state log, the path in UTF-8. WebAssembly has one thread, so the search
//! uses one.

pub mod encoding;

#[cfg(target_arch = "wasm32")]
mod exports;
