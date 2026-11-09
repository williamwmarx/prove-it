//! Native code from our own backend (native/design/native-backend.md). The `unsafe` the backend
//! needs lives in this module: [`memory`] maps, seals and frees the memory code runs from.

pub mod memory;
