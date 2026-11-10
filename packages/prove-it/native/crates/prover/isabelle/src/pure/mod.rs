//! Isabelle's Pure: terms, types, theorems, unification and the tactics built on them.

pub mod bicompose;
pub mod consts;
pub mod conv;
pub mod drule;
pub mod envir;
pub mod goal;
pub mod interrupt;
pub mod list;
pub mod logic;
pub mod name;
pub mod net;
pub mod pattern;
pub mod search;
pub mod seq;
pub mod table;
pub mod tactic;
pub mod tactical;
pub mod term;
pub mod term_ord;
pub mod thm;
pub mod types;
pub mod unify;
pub mod variable;

#[cfg(test)]
pub(crate) mod testing;
