//! Prove It's front end in Rust: from `.tla` and `.cfg` files to the engine IR, or to the
//! messages SANY and TLC print, as the TypeScript front end does. DESIGN.md section 14 plans it.

pub mod ast;
pub mod dump;
pub mod errors;
pub mod hash;
pub mod json;
pub mod lexer;
pub mod parser;

/// The version of TLC whose behaviour the front end reproduces, as `TlcVersion` in
/// `src/tlc/version.ts`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TlcVersion {
    Master,
    V1_7_4,
}
