# Prove It

Prove It checks TLA+ specs and TLAPS proofs without the JVM. It is a drop-in for TLC, SANY and tlapm: same options, same output, byte for byte. People trust a model checker's verdict without re-deriving it, so a wrong answer is worse than no answer.

## Layout

`packages/prove-it/native` is the Rust workspace and the product: the front end (`tla-front`), the engine (`tla-engine`, `tla-live`, `tla-trace`), the provers (`crates/prover/`) and the `prove-it` binary. `native/DESIGN.md` and `native/design/` explain each part. `packages/prove-it/src` is the TypeScript npm package that wraps the engine as a native addon and as WebAssembly. What TypeScript remains beyond that wrapper is being ported to Rust; do not add to it.

## The oracle

TLC, SANY and tlapm define correct. Before implementing anything, read their source (`tlaplus/tlaplus`, at the commit `TLC_COMMIT` names in `.depot/workflows/benchmark.yml`) and run the real tool on the spec. Never work from memory of TLA+ semantics.

Output either matches the reference byte for byte or the binary declines with `prove-it: not native yet: <reason>`. Something that matches today must never become a decline, unless it matched only by chance; such a run declines and is listed under "Declines to win back" in `native/design/fallback.md`. `native/design/fallback.md` lists every decline and every known wrong output; keep it true.

## Principles

Build for the long run. Judge a change by whether it improves the architecture, not by how small its diff is.

Rust uses the standard library only, and the npm package has no runtime dependencies.

No timeouts. A check runs until it finishes or the user stops it.

Never weaken a test, a recorded output or the known-differences list to get green. Fix the cause.

Speed matters, after correctness. Measure before and after on Depot with the benchmark `.depot/README.md` describes, never on a development machine.

Only comment on a constraint the code cannot express.

## Verifying

Bun 1.4.4 is the toolchain for everything outside `native`; the Rust toolchain is pinned in `rust-toolchain.toml`. Before handing work back, run `bun run typecheck`, `bun run lint`, `bun run format:check` and `bun run test`, and for Rust `cargo fmt --check`, `cargo clippy --locked --all-targets -- -D warnings` and `cargo test --locked` in `packages/prove-it/native`. A change to the front end, the engine or traces also needs a clean Parity run (`.depot/workflows/parity.yml`), which compares the whole corpus against recorded TLC output.

## Commits

Conventional commits, `type(scope): summary`, one concern per commit and PR. Branch names are at most three hyphenated words with no prefix. Commits, PRs and code name no model and carry no co-author trailer.
