//! Native code from our own backend (native/design/native-backend.md). The `unsafe` the backend
//! needs lives in this module: [`memory`] maps, seals and frees the memory code runs from. [`ir`] is
//! what code is emitted from, and [`x86_64`] encodes the instructions it's emitted as.

// N1 emits x86-64 from the IR behind PROVE_IT_NATIVE_CODE; until then only its tests use it.
#[cfg_attr(not(test), expect(dead_code, reason = "emitted from in N1"))]
pub(crate) mod ir;
pub mod memory;
#[cfg_attr(not(test), expect(dead_code, reason = "emitted from in N1"))]
pub(crate) mod x86_64;
