Prove It interprets and model checks TLA+ specs in TypeScript and Rust, without the JVM. It is derived from [tla-ts](https://github.com/aidenybai/tla-ts). `packages/prove-it` is the library. `packages/prove-it/tests/unit` holds its unit tests. `packages/prove-it/native` is the Rust workspace: the engine, the front end and the native `prove-it` binary, which `native/DESIGN.md` plans.

When implementing anything in this project, clone `tlaplus/tlaplus` locally and search TLC's source to understand the relevant TLA+ semantics. Do not rely on memory or assumptions.

## Prove It rules

- Match TLC's semantics. When behavior is unclear, run the spec through TLC and compare.
- Keep the public API small. Justify every new export.
- Throw named errors from `src/errors.ts` and let them propagate. Do not wrap them in helpers such as `fail()`.
- Do not add timeouts unless asked.
- Keep the library free of runtime dependencies. The Rust crates use the standard library only: no third-party crates.

## Toolchain

The repository is a Bun 1.4.4 workspace. Use Bun for everything:

- `bun install` installs; commit `bun.lock`.
- `bun run build` bundles `dist/` with `bun build` and emits type declarations with `tsc`.
- `bun run test` builds `dist/` and then runs `bun test`, since some tests run `dist/cli.js` and the workers. Import test APIs from `bun:test`.
- `bun run typecheck` runs `bun check`.
- `bun run lint` runs `bun lint` from a pinned Bun canary, because stable Bun 1.4.4 has no `bun lint` yet. `bun run format` runs `bun fmt`. Both read their settings from `bunfig.toml`.
- The Rust workspace in `packages/prove-it/native` pins its toolchain in `rust-toolchain.toml`. `bun scripts/platform-packages.ts build` builds the addon and the binary into `native/npm/<platform>`.
- The conformance and benchmark scripts run through `scripts/run.ts`, which bundles them with Bun and runs them under Node, whose V8 is much faster than JavaScriptCore on the SMT prover. Node 22 must be on the PATH.

## Verifying changes

Run `bun run typecheck`, `bun run lint`, `bun run format:check`, and `bun run test` before you finish. For Rust changes, also run `cargo fmt --check`, `cargo clippy --locked --all-targets -- -D warnings` and `cargo test --locked` in `packages/prove-it/native`.

## Branch names

Use a short branch name of at most three words, separated by hyphens. Do not use slashes or type prefixes such as `feat/` or `fix/`.

Examples: `parse-operators`, `fix-set-equality`, `cleanup-tests`.

## Commits and PR titles

Use conventional commit messages and PR titles: `type(scope): summary`.

Valid types are `feat`, `fix`, `docs`, `chore`, `refactor`, and `test`. Scopes are optional. Use the affected area when helpful, such as `parser`, `evaluator`, or `checker`.

Examples: `feat(parser): parse LET and IN`, `fix(evaluator): compare records by field`, `test: port TLC set tests`.

Keep each commit and PR to one concern. Never merge with failing CI, and merge only when asked.

## Style guide

- Keep code clean, elegant, and simple. YAGNI.
- Remove unused code. Don't repeat yourself.
- Use TypeScript for project-authored code outside `packages/prove-it/native`, which is Rust (`native/DESIGN.md` §12).
- Prefer `const`. Use ternaries or early returns instead of reassignment and `else`.
- Use arrow functions and kebab-case file names.
- Avoid `any`. Avoid `as` unless necessary.
- Never use star imports or alias imports, such as `import { resolve as pathResolve }`.
- Omit file extensions in relative imports: `./core`, not `./core.js`.
- Use TypeScript interfaces over types. Keep them at module scope.
- Rely on type inference. Add annotations only for exports.
- Do not extract single-use helpers or variables. Inline them at the call site unless the helper is reused, hides a complex boundary, or has a name that clarifies the caller.
- Do not comment unless necessary. Prefix hacks, such as a `setTimeout`, with `// HACK: reason`.
- Avoid `try`/`catch` where possible.
- Use descriptive names. Avoid one or two character names.
  - In `.map()`, use `innerX` instead of `x`.
  - Use `isMoved` instead of `moved`.
  - Use `get`, `set`, and `use` prefixes.
- Use dot notation instead of destructuring, so `obj.a` keeps its context.

## Testing

- Avoid mocks. Use `globalThis` only when nothing else works.
- Test behavior, not implementation. Do not copy logic into tests.
- Make tests deterministic.
- Prefer specs ported from `tlaplus/Examples` and TLC's own tests over synthetic fixtures.
- Never weaken a test to make it pass. Fix the cause.
- `bun test` runs in Bun, not Node. A test that needs Node, such as one that passes Node's flags, spawns `node` by name rather than `process.execPath`.
