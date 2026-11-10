//! Isabelle's Pure: terms, types, theorems, unification and the tactics built on them.

pub mod consts;
pub mod envir;
pub mod interrupt;
pub mod list;
pub mod logic;
pub mod name;
pub mod net;
pub mod pattern;
pub mod seq;
pub mod table;
pub mod term;
pub mod term_ord;
pub mod types;
pub mod unify;

#[cfg(test)]
pub(crate) mod testing;
