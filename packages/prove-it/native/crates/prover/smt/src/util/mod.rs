//! What `lp`, `nlsat` and the core share (design/prover.md, stage P3a): Z3's hashes and hash table,
//! three-valued truth, its random generator and resource limit, and the solver's errors. Big
//! integers and rationals are `prove_num`'s.
//!
//! `src/prover/smt/solver/array.ts` has no module here: `shrink` is `Vec::truncate`, `setAt` is a
//! `resize` before the write, and `grow` is a `Vec`'s own growth.

pub mod error;
pub mod hash;
pub mod hashtable;
pub mod lbool;
pub mod random_gen;
pub mod rlimit;
