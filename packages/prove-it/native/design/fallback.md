# Plan: no TypeScript engine fallback in the npm package

A plan for the owner, not yet built. Once the native engine ships for every platform
`scripts/platform-packages.ts` lists (linux x64 and arm64 with glibc and with musl, darwin arm64
and x64, win32 x64), what should `check` do where the addon still can't load? And what code goes
when the TypeScript engine stops being a fallback?

## The chain today

`check` (src/check.ts) tries, in order:

1. `getEngineIneligibility`. Some models never reach an engine: `PROVE_IT_ENGINE=0`, `-dump`,
   `-continue`, a periodic config, TLC 1.7.4, or properties in an instance. These go to the
   interpreter.
2. The native engine, under `PROVE_IT_ENGINE_BACKEND` `auto` (the default) or `rust`.
   `checkNatively` returns `complete`, `stopped`/`invariant` (with a checkpoint for the interpreter),
   `declined`, or `unavailable`.
3. The TypeScript engine (`runEngine` in src/engine/search.ts). It runs when the native engine is
   `unavailable` or `declined`, or when `PROVE_IT_ENGINE_BACKEND=ts`. It searches on one thread
   since #113.
4. The interpreter. It goes on from where the TypeScript engine bails, and it prints every trace
   and checks what the engines hand over.

`loadAddon` in src/engine/native.ts gives one of these reasons when it reports `unavailable`:
- no platform package resolved;
- no `process.dlopen`;
- `dlopen` threw (wrong libc, missing file, or, on Windows, an N-API function the host doesn't
  export, #126);
- the addon's ABI version isn't the loader's.

This plan is about step 3 as the answer to `unavailable`. Step 3 as the answer to `declined` goes
away only when the native engine declines nothing (the gaps workstream). That is a prerequisite
below, not part of this decision.

## Who still has no addon once all seven ship

- **Unlisted platforms.** linux riscv64, ppc64le, s390x and 32-bit arm, win32 arm64, FreeBSD,
  Android (Termux), illumos.
- **Optional dependencies not installed.**
  - `npm install --omit=optional` (or `--no-optional`), `yarn --ignore-optional`, or a pnpm
    `supportedArchitectures` that leaves the platform out.
  - A lockfile written on another platform, under npm's known optional-dependency bug
    (npm/cli#4828).
  - A copy of `dist/` vendored without `node_modules`.
- **Version skew.** A platform package from another release gives an ABI mismatch.
- **Hosts without `process.dlopen`.** A browser bundle of the library, or a runtime without Node's
  addon API.

Nothing measures how many users these cover. The first three are user error or rare platforms, and
the last can't run the CLI at all.

## Options

- **A. Fail loudly.** Throw a named error, for example `NativeEngineUnavailableError` in
  src/errors.ts. It names the platform triple, the package `check` looked for, and the loader's
  reason, then says how to fix it: reinstall with optional dependencies, or use a supported
  platform. The CLI prints it and exits non-zero.
- **B. Keep the TypeScript engine as a last resort.** This is today's behavior, plus a one-line
  warning on stderr that the native engine is missing and the check is slower. It is correct and
  only slow, but it keeps about 7,000 lines and their tests alive for a few users.
- **C. Fail loudly, with the interpreter as the explicit escape hatch (recommended).** As in A, but
  the message also names `PROVE_IT_ENGINE=0`. That setting runs the reference interpreter, which
  stays in any case: it is the test oracle and the trace printer. Nobody is stranded, the slow path
  is a choice the user makes, and the TypeScript engine has no remaining role.

## Prerequisites before deleting the TypeScript engine

1. **All seven platform packages are published, each with an install test in CI.**
   - Shipped in 0.2.4: linux x64 and arm64 gnu, darwin arm64 and x64, and win32 x64 (#126, #129).
   - Built and tested in CI by #147: the musl x64 and arm64 packages. Release.yml publishes them
     once #156 merges.
2. **The native engine declines nothing in the corpora and fixtures.** Today a decline falls back
   to the TypeScript engine. Afterwards it would go straight to the interpreter, which is correct
   but much slower, so the decline count should be zero first. It is tracked by Parity's engine
   coverage and the gaps workstream.
3. **The Parity pairs that name the TypeScript engine have native replacements that already
   match.** `tlc/ts` becomes `tlc/rust`, and `ts/stopped` gives way to `rust/stopped`. `ts/rust`
   and `ts/interpreter` are retired.
4. **The handover to the interpreter no longer goes through the TypeScript store.** Today
   `native.ts` decodes the native states into TypeScript store ids for checkpoints. Until the trace
   evaluator and the CLI workstream carry that, `store.ts`, `convert.ts` and `fingerprint.ts` stay
   (below).

## What it deletes

The TypeScript engine's search and compiler, about 6,800 of src/engine's 10,800 lines:

- `src/engine/compile.ts`, `action.ts`, `codegen.ts` and `memo.ts`.
- `src/engine/search.ts`'s `runEngine`. `EngineCheckpoint` and `EngineResult` move to `native.ts`.
- `src/engine/context.ts`. `EngineSpec`, `EngineProperties` and `toEngineProperties`, which
  `ir.ts` and `check.ts` use, move to `ir.ts`.
- `src/engine/symmetry.ts`'s canonicalizer (`NamedPermutation` stays with `ir.ts`).
- `src/engine/live.ts`'s `createLiveOracle` (the `LiveOracle` type stays).
- `src/engine/state-log.ts`, since the native search writes the same log (`search.rs`).
- In `src/check.ts`: the `runEngine` branch, the `PROVE_IT_MEMO` report, the `ts` value of
  `PROVE_IT_ENGINE_BACKEND` and the `auto`/`rust` distinction, and `getNativeOnlyReason`.
  `unavailable` becomes the error from option C.
- In `src/engine/settings.ts`: `PROVE_IT_CODEGEN` (and with it the ahead-of-time binary's closure
  path), `PROVE_IT_FINGERPRINT`, and `PROVE_IT_STORE_TRACE`.
- Tests:
  - every entry of `native/ts-only-tests.json`;
  - `store-trace.test.ts`;
  - the `ts` cases in `engine.test.ts` and `native.test.ts`;
  - the `ts` cases of the other tests that pin `PROVE_IT_ENGINE_BACKEND=ts`; their native cases
    stay.
- Scripts: the `ts` backend in `engine-coverage.ts` and `engine-runs.ts`, `store-replay.ts`, and
  the `ts` pairs in `differential.ts`.

Stays:
- `ir.ts`: the TypeScript front end's lowering, until the Rust front end's F8 replaces it.
- `store.ts`, `convert.ts`, `fingerprint.ts` and `native-store.ts`: the bridge to the interpreter
  and the store tests' oracle, until prerequisite 4.
- `native.ts` and `settings.ts`'s remaining settings.
- The interpreter, and with it `PROVE_IT_ENGINE=0`.

## For the owner to decide

1. Is it A, B or C? (Recommended: C.)
2. The CLI's exit code for a missing engine. TLC has none of its own; 255, as for an internal
   error, or a new one.
3. Whether a browser build of the library is a supported use. If it is, the library needs C's
   escape hatch by default there (the interpreter), or a WebAssembly build of the engine.
4. The order. Prerequisites 1 and 2 come first; deleting the code is then about three PRs: the
   search and compiler, the settings and scripts, then the tests and Parity pairs.
