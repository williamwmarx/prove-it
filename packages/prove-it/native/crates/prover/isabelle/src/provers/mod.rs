//! Isabelle's generic provers: the classical reasoner and blast, its tableau prover.

pub mod blast;
pub mod classical;
pub mod hypsubst;

#[cfg(test)]
pub(crate) mod testing;
