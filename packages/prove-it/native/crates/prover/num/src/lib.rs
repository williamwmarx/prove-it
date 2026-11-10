//! Big integers and rationals with the semantics of JavaScript's `bigint` that the TypeScript SMT
//! solver relies on (`src/prover/smt/solver/rational.ts`): `/` truncates toward zero, `%` takes
//! the dividend's sign and `>>` floors. Stage P3a of design/prover.md ports it.
