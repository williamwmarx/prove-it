//! Prove It's front end in Rust: from `.tla` and `.cfg` files to the engine IR, or to the
//! messages SANY and TLC print, as the TypeScript front end does. DESIGN.md section 14 plans it.

pub mod errors;
pub mod hash;
pub mod json;
pub mod lexer;
