# SMT tables

These tables were recorded from the TypeScript SMT solver (`src/prover/smt/solver/`) at commit
f5b7bef, before it was deleted, by the now-deleted scripts that wrote them:

- `hash.txt`, `hashtable.txt`, `hashtable-operations.txt` and `random-gen.txt`:
  `scripts/smt-foundation-tables.ts`
- `ast.txt`: `scripts/smt-core-tables.ts`
- `parser.txt`: `scripts/smt-parser-tables.ts`
- `rewriter.txt`: `scripts/smt-rewriter-tables.ts`
- `th-rewriter.txt`: `scripts/smt-th-rewriter-tables.ts`
- `nnf.txt`: `scripts/smt-nnf-tables.ts`
- `tactics.txt`: `scripts/smt-tactics-tables.ts`
- `models.txt`: `scripts/smt-model-reference.ts`
- `mbqi.txt`: `scripts/smt-mbqi-reference.ts`
- `lra.txt`: `scripts/smt-lra-reference.ts`
- `decide.txt`: `scripts/smt-decide-reference.ts`

They are frozen expected data. Nothing rewrites them now: a change to a line is a change to the
solver's behaviour.
