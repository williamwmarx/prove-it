# No TypeScript engine fallback

What `check` does where the native engine declines a model or can't be loaded, now that the
TypeScript engine is deleted. The plan was written for the owner on 2026-11-09 (branch
`fallback-plan`); the owner chose option C below the same day, and this records it as built.

## The chain

`check` (src/check.ts) tries, in order:

1. `getEngineIneligibility`. Some models never reach the engine: `PROVE_IT_ENGINE=0`, `-dump`,
   `-continue`, a periodic config and TLC 1.7.4. A spec without an initial predicate or a
   next-state relation doesn't either. The interpreter checks these, as TLC's semantics need and
   as the user asked.
2. The native engine (`checkNatively` in src/engine/native.ts). It returns:
   - `complete`: the search, which the interpreter replays only to check temporal properties and
     print a counterexample;
   - `stopped` or `invariant`: a violation, a deadlock or a run-time stop, with the search so far
     as a checkpoint the interpreter goes on from to print TLC's trace;
   - `declined`: the engine produced no state, and the interpreter checks the whole model;
   - `unavailable`: no engine loads, and `check` throws `EngineUnavailableError`.
3. The interpreter, which is the reference: it checks what the engine declines, goes on from a
   stop, and prints every trace.

The TypeScript engine was step 3 before, between the native engine and the interpreter. It is
gone, with `PROVE_IT_ENGINE_BACKEND`, `PROVE_IT_CODEGEN`, `PROVE_IT_STORE_TRACE` and
`PROVE_IT_MEMO`'s report. A decline now goes straight to the interpreter, which is correct but much
slower; the gaps workstream ([gaps.md](gaps.md)) takes the declines to zero.

## Where no engine loads (option C)

`getNativeAddon` loads, in order:

- the module `PROVE_IT_ENGINE_WASM` names, if set;
- where there is `process.dlopen` (Node, Bun): the addon `PROVE_IT_ENGINE_ADDON` names, the one an
  executable embeds, or the one in the platform package installed for this system; failing those,
  the WebAssembly engine the main package ships as `dist/prove-it-engine.wasm`, so an unlisted
  platform (riscv64, FreeBSD, win32 arm64 and so on), or an install without optional
  dependencies, still searches natively, on one thread. An addon named by `PROVE_IT_ENGINE_ADDON`
  or embedded is the only one tried;
- where there is none (a browser): the WebAssembly engine `loadWasmEngine` fetched and compiled
  before the check from beside the module, where a bundler copies it (DESIGN.md 7.4).

Where none loads, `check` throws `EngineUnavailableError` (src/errors.ts, exported). Its message
gives the loader's reason and says to install the package with its optional dependencies on a
supported platform, or to set `PROVE_IT_ENGINE=0` to check with the interpreter. The CLI prints it
and exits with 255, TLC's exit code for an internal error. Nothing falls back to a slower search
unasked.

Who reaches the error, now that the main package carries the WebAssembly engine: a host where it
fails to compile or instantiate, a build of `dist/` without it (`bun run build` alone, without
`platform-packages.ts build --target wasm32-unknown-unknown`), and a platform package from another
release (an ABI mismatch) where the addon is named or embedded.

### Decision: SANY's report needs the engine too

Settled on 2026-11-10, as the TypeScript SANY front end is retired (front.md): the CLI prints
SANY's report as tla-front writes it, through the addon or the WebAssembly engine. Once
`src/sany` is deleted, `PROVE_IT_ENGINE=0` means that the interpreter searches, not that no native
code runs: SANY's report still needs the addon or the WebAssembly engine. Where neither loads, the
CLI throws `EngineUnavailableError` for the report, worded for the front end, as `check` does for
the search. Until then, the CLI prints the TypeScript report where no engine loads.

The engine reads nothing itself: an export that reads what JavaScript holds, such as a spec's
modules, names what it needs and is called again with it (`prove-it-host`'s `sources`), so the
WebAssembly engine needs no file system and calls nothing in JavaScript.

### Decision: the WebAssembly engine ships in the main package

Settled on 2026-11-10 (#166): the engine as WebAssembly ships inside `@atemp/prove-it` as
`dist/prove-it-engine.wasm`, not as a separate `@atemp/prove-it-wasm32` package. A browser bundler
copies only an asset a literal `new URL("./…", import.meta.url)` names beside the module that names
it, as it copies the workers, and a browser can't resolve a bare package specifier without an
import map, so a separate package was never found once bundled. It costs every install about
1.3 MB, and in return every install has an engine: the browser's, and Node's or Bun's where no
platform addon loads.

## Where the interpreter remains a fallback

- **A decline.** The engine declined before producing any state.
- **A stop.** A violation or a deadlock hands over the search so far, and the interpreter prints
  TLC's trace from it. A run-time stop the engine doesn't model does the same.
- **A WebAssembly trap.** The engine's frames are on the host's call stack there, which is
  shallower than the addon's search thread, so a deep recursion can trap. The loader replaces the
  instance and returns a stop that hands nothing over, and the interpreter searches from the start
  (src/engine/wasm.ts). This is the one fallback that is not a semantic hand-over; it stays until
  the engine's recursion no longer runs on the host's stack.

Each of these reports itself under `PROVE_IT_ENGINE=debug` (`native: declined: …`,
`handed over after …`).

## What was deleted

The TypeScript engine's search and compiler, about 7,400 lines: `src/engine/compile.ts`,
`action.ts`, `codegen.ts`, `memo.ts`, `context.ts`, `search.ts`, `live.ts`, `symmetry.ts` and
`state-log.ts`. The types the native path still uses (`EngineCheckpoint`, `EngineResult`,
`EngineGraph`, `LiveOracle`) moved to `native.ts`, and `IrSpec` to `ir.ts`.

With it went its tests (the memo tables, the store trace, `ts-only-tests.json`), the scripts that
read its internals (`native-expressions.ts`, `native-replay.ts`, `store-replay.ts`), the `ts`
backend of the conformance scripts and the Parity pairs that named it (`ts/rust`, `tlc/ts`,
`ts/interpreter`, `ts/stopped`), and `coverage-allowlist.json`, which gated the native engine's
coverage against it. The native search tests that compared state logs with it now compare the
native state log with the states the interpreter writes to TLC's `-dump`, in TLC's order.

What stays: `ir.ts` (the TypeScript front end's lowering, until `tla-front` replaces it);
`store.ts`, `convert.ts` and `fingerprint.ts`, the bridge that decodes the native states for the
interpreter and the store tests' oracle; `native.ts`, `wasm.ts` and `settings.ts`; and the
interpreter, with `PROVE_IT_ENGINE=0`.

## Tests need the engine

Every check needs an engine, so `bun run test` builds the addon for this system
(`platform-packages.ts build`) before it runs, and `tests/setup.ts`, which `bunfig.toml` preloads,
points `PROVE_IT_ENGINE_ADDON` at it unless it or `PROVE_IT_ENGINE_WASM` is set. Running the tests
needs the pinned Rust toolchain; Verification's Test task and Release's test step bootstrap it.

## Retiring the interpreter

The owner asked on 2026-11-10 for the interpreter to go too, after the TypeScript SANY front end
and alongside the prover's port to Rust. This is the plan. Nothing is deleted until its stages
are green.

### Measured on main

- **The library declines 15 models** of the 733 Conformance models TLC checks in 20 s or less, each
  under a second:
  - TLCSet (8): ConstantContextTLCCache, DieHardTLA, EWD998Chan, TLCGetNonDeterminism, TLCSetInit,
    Test2, ChainedCdots and NQSpec/MC;
  - TLCGet (2): MCDieHardest and test220;
  - printing a value whose text depends on how TLC built it (2): FastMutex2 and FastMutex3;
  - JsonSerialize (1): EWD840_json;
  - AssertError (1): Github696;
  - a definition TLC computes at startup that fails there (1): test23.
- **The binary prints what TLC prints for all 15.** The native-only differential runs 1466 runs
  (733 models in two modes). 1460 print what TLC prints and the other 6 are known differences. None
  says `not native yet`.
- **The engine already covers the corpus.** The interpreter survives because the library doesn't run
  the binary's pipeline. The library lowers the engine IR from the interpreter's `Environment`
  (`src/engine/ir.ts` imports `evaluate`, `liveness` and `values`), and prints through the
  interpreter. The binary goes from `tla-front` to the IR, the engine, and `tla-trace` and
  `tla-live`, and prints TLC's output itself.

### What the interpreter still does

Besides the 15 declines, it does the following in the library:

- **Stops.** 131 of those models stop: a deadlock (54), an invariant (33), an initial state (7) or
  a run-time error (about 37). The interpreter re-derives the expanding state and prints TLC's trace
  (`resumeFromEngine`, `tlc/replay.ts`). The binary prints these natively (`tla-trace`).
- **Temporal properties.** The interpreter prints the lasso or accepting counterexample from the
  native graph. Under SYMMETRY or a VIEW, or where `tla-live` declines, it checks the properties
  again. The binary prints lassos and accepting counterexamples, including a lasso under SYMMETRY or
  a VIEW, whose states it re-creates from the previous real state's successors as TLC's
  `LiveWorker.printTrace` does with `getState(fp, previous)`. It declines an accepting node under
  SYMMETRY or a VIEW, an unexpanded graph and uncounted branches. None of these occurs in the
  corpus or the library's tests ([below](#liveness)).
- **Models without a search.** 44 models have only constants and ASSUMEs. The interpreter also
  checks every model's assumptions, and computes the initial states of a spec without a next-state
  relation. The binary does all three.
- **What `getEngineIneligibility` keeps from the engine:** `PROVE_IT_ENGINE=0`, `-dump`, `-continue`,
  a periodic config and TLC 1.7.4. The binary says `not native yet` to `-dump`, `-continue` and
  TLC 1.7.4. The engine doesn't support a periodic config either.
- **A WebAssembly stack overflow.** The interpreter searches from the start.
- **`PROVE_IT_LIVE_CHECK=1`.** It cross-checks the native liveness verdict.

Neither side implements `-simulate`, `-generate`, `-debug`, `-dumpTrace` or `-loadTrace`.
`src/pcal` only validates for SANY, `src/obligations` imports nothing from the interpreter, and
`src/prover` imports only `worker.ts`'s thread helpers (`isWorkerSupported`, `spawnWorker`,
`getParentPort`). Those move to the prover. `tlc/version.ts`, `tlc/jar-data.ts` and
`tlc/messages.ts` are shared with the front end and the CLI, so they move too.

### Every `check` of the library's tests, through the binary

`bun scripts/run.ts check-log` measures this; it is the retirement's progress meter. It runs
`bun test` with `PROVE_IT_CHECK_LOG`, under which each `check` given its configuration as text writes
its source, configuration, options and calling test, and each module it loads. Then it runs each
distinct check through the binary with TLC's command line for its options: the seed, `-lncheck`,
`-tool`, `-dump`, `-continue` and TLC 1.7.4. Each check runs on one thread and with every level
shared between four. `--json` writes each check with its answers.

Measured at main 6871cd2:

- 1,784 checks. 1,163 print TLC's output natively. Their exit codes are 0 (507), 150 (168), 12
  (103), 10 (96), 75 (94), 13 (80), 151 (52), 255 (28), 11 (12), 76 (9), 14 (8) and 77 (6).
- 621 are `not native yet`, for 196 reasons, grouped below and listed in full after.
- One thread and four gave the same answer for every check.
- None used `-continue`.
- Not measured: checks whose configuration is an object, and the CLI tests' own runs of
  `dist/cli.js`.

| Kind | Runs | Reasons | Test files (runs) |
|---|---:|---:|---|
| Rebuilding a run-time failure | 161 | 60 | `check` 58, `engine` 49, `native-builtins` 29, `native-search` 8, `tlc-replay` 4, `operator-constants` 4 … |
| The command line (`-dump`, TLC 1.7.4) | 131 | 2 | `check` 50, `native-sets` 29, `native-search` 19, `native-builtins` 15, `state-graph` 7, `tlc-replay` 5 … |
| Rebuilding a failing assumption | 95 | 39 | `check` 70, `bags` 18, `json` 2, `exit-codes` 1, `modules` 1, `tlc-action` 1 … |
| The engine stops the search | 86 | 34 | `check` 31, `native-builtins` 17, `engine` 8, `exit-codes` 6, `native-search` 5, `tlc-replay` 4 … |
| The engine declines the model | 48 | 21 | `check` 12, `native-search` 10, `native-sets` 7, `tlc-ext-operators` 6, `engine-print` 4, `operator-constants` 3 … |
| Temporal properties | 40 | 20 | `check` 12, `native-search` 8, `tlc-replay` 4, `tlc-live-level` 4, `engine` 3, `temporal` 3 … |
| Front end, configuration and printing | 33 | 13 | `check` 13, `engine-print` 5, `alias` 4, `native-search` 3, `printing` 3, `possible` 3 … |
| Constant evaluation | 27 | 7 | `check` 10, `engine` 5, `native-search` 3, `exit-codes` 2, `bags` 2, `tlc-replay` 1 … |

#### Liveness

306 of the checks have temporal properties: 203 are native and 103 are not. 43 of those 103 are the
liveness part of this plan:
- an atom of the temporal properties that may fail to evaluate (14), and a failure in a model with
  temporal properties (3);
- the search's stops in a model with temporal properties: deadlock (3), an invariant (1), a
  division by zero (1);
- a property TLC finds a tautology (3), or a constant part of a temporal formula that isn't a
  boolean (2);
- printing where the native checker doesn't check the temporal properties (5);
- a lasso the engine doesn't hand over (5);
- an atom the engine doesn't answer (2);
- a late node at another diameter, a step back into the cycle of a spec that prints, several states
  under VIEW or SYMMETRY, and a lasso TLC fails to rebuild under a VIEW (1 each).

Of the other 60:
- 27 decline on the command line (TLC 1.7.4, 24; `-dump`, 3);
- 6 are the action property violated, for `-continue`'s native report;
- the rest are constant evaluation, a constraint or VIEW that fails on a successor, and the
  evaluator's other gaps.

The corpus has no temporal decline: `differential --native-only` matches 1,460 of 1,466 runs, and
the 6 known differences aren't about liveness.

A lasso that ends in the first state of its cycle (the `temporal` test's three runs) is more than a
printing gap. Printing it as TLC does, stuttering at the cycle's first state, matches TLC built at
d8fb231 on those three runs. But on the binary's own `lasso-end` case the lasso differs from TLC's,
so the decline stays until the lasso's construction is traced against `LiveWorker.printTrace`.

Nothing reaches these liveness declines, so they stay declines until a test or a model does:
- an accepting node under SYMMETRY or a VIEW;
- an unexpanded graph;
- uncounted branches;
- every decline of atoms that read or set TLC's registers.

#### Every reason

| Runs | Reason | Tests |
|---:|---|---|
| 69 | -dump | `unit/native-sets.test.ts:86` ×29, `unit/native-builtins.test.ts:222` ×15, `unit/state-graph.test.ts:22` ×6, `unit/native-search.test.ts:301` ×2, `unit/native-search.test.ts:666`, `unit/native-search.test.ts:527`, `unit/native-search.test.ts:49`, `unit/native-search.test.ts:159`, `unit/native-search.test.ts:169`, `unit/native-search.test.ts:234`, `unit/native-search.test.ts:323`, `unit/native-search.test.ts:607`, `unit/native-search.test.ts:219`, `unit/native-search.test.ts:243`, `unit/native-search.test.ts:363`, `unit/native-search.test.ts:603`, `unit/native-search.test.ts:711`, `unit/native-search.test.ts:542`, `unit/native-search.test.ts:385`, `unit/native-search.test.ts:133`, `unit/native-search.test.ts:192` |
| 62 | TLC 1.7.4 | `unit/check.test.ts:2573` ×5, `unit/check.test.ts:5116` ×3, `unit/check.test.ts:129` ×3, `unit/check.test.ts:5562` ×2, `unit/tlc-replay.test.ts:40` ×2, `unit/check.test.ts:1353` ×2, `unit/check.test.ts:2521` ×2, `unit/check.test.ts:5481` ×2, `unit/check.test.ts:2035`, `unit/check.test.ts:5266`, `unit/state-graph.test.ts:22`, `unit/check.test.ts:3519`, `unit/check.test.ts:1329`, `unit/check.test.ts:5309`, `unit/check.test.ts:5276`, `unit/check.test.ts:5361`, `unit/parallel.test.ts:18`, `unit/check.test.ts:111`, `unit/check.test.ts:5346`, `unit/modules.test.ts:157`, `unit/check.test.ts:5354`, `unit/check.test.ts:5414`, `unit/check.test.ts:5451`, `unit/check.test.ts:2508`, `unit/check.test.ts:5437`, `unit/check.test.ts:2466`, `unit/check.test.ts:5247`, `unit/check.test.ts:5524`, `unit/check.test.ts:1980`, `unit/check.test.ts:5384`, `unit/check.test.ts:5316`, `unit/tlc-replay.test.ts:225`, `unit/check.test.ts:2339`, `unit/check.test.ts:1485`, `unit/randomization.test.ts:162`, `unit/liveness.test.ts:111`, `unit/liveness.test.ts:97`, `unit/check.test.ts:5259`, `unit/check.test.ts:5234`, `unit/check.test.ts:5423`, `unit/tlc-replay.test.ts:167`, `unit/check.test.ts:5465`, `unit/check.test.ts:5407`, `unit/check.test.ts:5370`, `unit/tlc-replay.test.ts:185`, `unit/check.test.ts:5399`, `unit/check.test.ts:2046`, `unit/modules.test.ts:152`, `unit/check.test.ts:5239` |
| 14 | a constant invariant the engine checks, which TLC may warn about | `unit/engine.test.ts:46` ×3, `unit/bags.test.ts:43` ×2, `unit/engine.test.ts:807` ×2, `unit/native-search.test.ts:1519`, `unit/native-search.test.ts:1513`, `unit/tlc-replay.test.ts:197`, `unit/native-search.test.ts:1931`, `unit/engine-print.test.ts:31`, `unit/instances.test.ts:43`, `unit/exit-codes.test.ts:10` |
| 14 | the engine stopped: a constraint, a VIEW or an action property that fails on a successor | `unit/exit-codes.test.ts:10` ×3, `unit/check.test.ts:2983` ×2, `unit/tlc-replay.test.ts:40` ×2, `unit/check.test.ts:2002`, `unit/check.test.ts:2081`, `unit/possible.test.ts:110`, `unit/check.test.ts:2013`, `unit/check.test.ts:2046`, `unit/check.test.ts:2026`, `unit/check.test.ts:2071` |
| 12 | the engine stopped: a mistyped membership in a set of functions: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/engine.test.ts:765` ×12 |
| 11 | the engine declined: unsupported: Print | `unit/native-search.test.ts:1306` ×7, `unit/engine-print.test.ts:31` ×4 |
| 11 | the engine stopped: values TLC can't compare: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/engine.test.ts:765` ×5, `unit/engine.test.ts:46` ×3, `unit/check.test.ts:1675` ×2, `unit/check.test.ts:1576` |
| 10 | the engine stopped: a mistyped membership in a set of records: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/engine.test.ts:765` ×10 |
| 9 | an assumption that fails to evaluate: evaluating the assumption again: expected an integer, not a string | `unit/check.test.ts:2330` ×4, `unit/check.test.ts:3159` ×4, `unit/check.test.ts:2593` |
| 9 | printing a value whose text depends on how TLC built it | `unit/engine-print.test.ts:31` ×5, `unit/printing.test.ts:7` ×3, `unit/native-search.test.ts:1229` |
| 9 | the engine declined: unsupported: enumerating a set TLC keeps lazy (UNION at line 3) | `unit/native-sets.test.ts:248` ×4, `unit/check.test.ts:5217` ×2, `unit/check.test.ts:5206` ×2, `unit/native-sets.test.ts:311` |
| 9 | the engine stopped: a conjunct that isn't a boolean: evaluating the failure again: expected a boolean, not a integer | `unit/check.test.ts:2368` ×6, `unit/check.test.ts:2961` ×2, `unit/check.test.ts:382` |
| 9 | the engine stopped: division by zero: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/check.test.ts:1699` ×4, `unit/native-search.test.ts:505`, `unit/check.test.ts:1980`, `unit/check.test.ts:1797`, `unit/check.test.ts:1991`, `unit/check.test.ts:1809` |
| 8 | an assumption that fails to evaluate: evaluating the assumption again: integer overflow | `unit/check.test.ts:2330` ×6, `unit/check.test.ts:2612` ×2 |
| 7 | an assumption that fails to evaluate: evaluating the assumption again: expected a boolean, not a integer | `unit/check.test.ts:2675` ×5, `unit/check.test.ts:2330` ×2 |
| 7 | the engine stopped: a membership in SUBSET of a non-set: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/engine.test.ts:765` ×7 |
| 6 | the engine stopped: a mistyped membership in a set of tuples: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/engine.test.ts:765` ×6 |
| 6 | the engine stopped: a mistyped membership in Seq: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/engine.test.ts:765` ×6 |
| 6 | the engine stopped: a power set too large to build | `unit/engine.test.ts:1149` ×4, `unit/engine.test.ts:680`, `unit/engine-print.test.ts:31` |
| 6 | the engine stopped: an action property violated | `unit/native-search.test.ts:1146`, `unit/check.test.ts:974`, `unit/check.test.ts:5309`, `unit/check.test.ts:5172`, `unit/parallel.test.ts:18`, `unit/check.test.ts:579` |
| 6 | the engine stopped: ToString of a value whose text depends on how TLC built it | `unit/native-builtins.test.ts:244` ×6 |
| 5 | a POSTCONDITION or an ALIAS TLC may compute as it starts | `unit/alias.test.ts:72` ×2, `unit/alias.test.ts:89`, `unit/possible.test.ts:118`, `unit/possible.test.ts:123` |
| 5 | a temporal property's counterexample: a lasso the engine doesn't hand over | `unit/temporal.test.ts:96` ×3, `unit/native-search.test.ts:1027`, `unit/engine-print.test.ts:31` |
| 5 | an assumption that fails to evaluate: evaluating the assumption again: it didn't fail | `unit/check.test.ts:194`, `unit/bags.test.ts:97`, `unit/check.test.ts:3125`, `unit/check.test.ts:2776`, `unit/check.test.ts:2330` |
| 5 | an assumption that fails to evaluate: evaluating the assumption again: SUBSET of a non-set | `unit/check.test.ts:2330` ×4, `unit/check.test.ts:2583` |
| 5 | an assumption that fails to evaluate: evaluating the assumption again: the builtin BagOfAll | `unit/bags.test.ts:128` ×3, `unit/bags.test.ts:97`, `unit/bags.test.ts:107` |
| 5 | the engine declined: unsupported: enumerating a set TLC keeps lazy (UNION at line 5) | `unit/check.test.ts:5116` ×2, `unit/check.test.ts:5145`, `unit/native-sets.test.ts:322`, `unit/check.test.ts:1606` |
| 5 | the engine stopped: an atom of the temporal properties that may fail to evaluate | `unit/tlc-live-level.test.ts:18` ×2, `unit/tlc-replay.test.ts:225`, `unit/tlc-live-level.test.ts:25`, `unit/engine.test.ts:1149` |
| 5 | the engine stopped: an atom of the temporal properties that may fail to evaluate: evaluating the failure again: expected a boolean, not a integer | `unit/check.test.ts:2428` ×2, `unit/check.test.ts:2443` ×2, `unit/tlc-replay.test.ts:40` |
| 5 | the engine stopped: an operator's table applied outside its rows: evaluating the failure again: an operator's table applied outside its rows | `unit/operator-constants.test.ts:81` ×3, `unit/native-search.test.ts:1801`, `unit/operator-constants.test.ts:49` |
| 5 | the engine stopped: enumerated Nat | `unit/check.test.ts:3101` ×2, `unit/check.test.ts:1934` ×2, `unit/check.test.ts:1951` |
| 4 | a _POSSIBLE predicate the search didn't witness | `unit/native-search.test.ts:1547`, `unit/native-search.test.ts:1540`, `unit/possible.test.ts:66`, `unit/check.test.ts:282` |
| 4 | an assumption that fails to evaluate: evaluating the assumption again: expected an integer, not a set | `unit/check.test.ts:2330` ×4 |
| 4 | rebuilding a trace: the builtin Trace | `unit/alias.test.ts:28`, `unit/tlc-ext.test.ts:23`, `unit/alias.test.ts:48`, `unit/alias.test.ts:59` |
| 4 | the engine stopped: applied a function outside its domain: evaluating the failure again: applied a function outside its domain | `unit/check.test.ts:1830`, `unit/check.test.ts:1896`, `unit/check.test.ts:1874`, `unit/native-search.test.ts:505` |
| 4 | the engine stopped: expected a boolean: evaluating the failure again: expected a boolean, not a function | `unit/check.test.ts:1403` ×4 |
| 4 | the engine stopped: recursion too deep | `unit/exit-codes.test.ts:10` ×3, `unit/check.test.ts:2928` |
| 4 | the engine stopped: SubSeq outside the sequence's domain: evaluating the failure again: SubSeq outside the sequence's domain | `unit/native-builtins.test.ts:228` ×4 |
| 4 | the engine stopped: unsupported: comparing a function TLC keeps lazy | `unit/native-search.test.ts:505` ×3, `unit/native-builtins.test.ts:228` |
| 4 | the engine stopped: unsupported: TLCGet of a key the search doesn't keep | `unit/check.test.ts:2837`, `unit/check.test.ts:5370`, `unit/tlc-statistics.test.ts:25`, `unit/check.test.ts:248` |
| 4 | values TLC can't compare, which the constant evaluator doesn't compute | `unit/check.test.ts:1257` ×3, `unit/exit-codes.test.ts:10` |
| 3 | a constant definition the configuration names | `unit/check.test.ts:5011`, `unit/check.test.ts:5014`, `unit/check.test.ts:5019` |
| 3 | a division by zero, which the constant evaluator doesn't compute | `unit/check.test.ts:1300`, `unit/check.test.ts:5507`, `unit/liveness.test.ts:111` |
| 3 | a property TLC finds a tautology | `unit/check.test.ts:5194`, `unit/check.test.ts:5524`, `unit/check.test.ts:5316` |
| 3 | a SYMMETRY definition that isn't an operator applied to its sets | `unit/check.test.ts:1243` ×2, `unit/exit-codes.test.ts:10` |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: a membership in a set, which isn't a set | `unit/check.test.ts:2760`, `unit/check.test.ts:2717`, `unit/check.test.ts:2754` |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: enumerated an infinite set | `unit/bags.test.ts:97` ×2, `unit/check.test.ts:2675` |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: expected a sequence, not 1 | `unit/check.test.ts:2330` ×2, `unit/check.test.ts:2339` |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: expected an integer, not a function | `unit/check.test.ts:2330` ×3 |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: the builtin AssertEq | `unit/check.test.ts:770` ×2, `unit/json.test.ts:11` |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: the builtin SubBag | `unit/bags.test.ts:97`, `unit/check.test.ts:501`, `unit/bags.test.ts:120` |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: values TLC can't compare | `unit/check.test.ts:3248` ×3 |
| 3 | temporal quantification in the specification | `unit/specifications.test.ts:68` ×2, `unit/exit-codes.test.ts:10` |
| 3 | the engine declined: unsupported: PickSuccessor | `unit/tlc-ext-operators.test.ts:11` ×2, `unit/tlc-ext-operators.test.ts:61` |
| 3 | the engine stopped: a guard that isn't a boolean: evaluating the failure again: expected a boolean, not a integer | `unit/tlc-replay.test.ts:40`, `unit/check.test.ts:2961`, `unit/exit-codes.test.ts:10` |
| 3 | the engine stopped: a predicate that isn't a boolean: evaluating the failure again: expected a boolean, not a integer | `unit/check.test.ts:2071` ×2, `unit/check.test.ts:2002` |
| 3 | the engine stopped: an order of strings the search ranked | `unit/native-builtins.test.ts:279` ×2, `unit/native-builtins.test.ts:327` |
| 3 | the engine stopped: applied a function outside its domain: evaluating the failure again: values TLC can't compare | `unit/check.test.ts:2573` ×3 |
| 3 | the engine stopped: deadlock | `unit/tlc-replay.test.ts:185`, `unit/check.test.ts:2521`, `unit/tlc-replay.test.ts:167` |
| 3 | the engine stopped: enumerated a set TLC can't enumerate: evaluating the failure again: enumerated an infinite set | `unit/check.test.ts:2407`, `unit/check.test.ts:3043`, `unit/check.test.ts:1914` |
| 3 | the engine stopped: expected a set: evaluating the failure again: expected a set, not a integer | `unit/native-builtins.test.ts:228` ×3 |
| 3 | the engine stopped: expected an integer: evaluating the failure again: expected an integer, not a string | `unit/tlc-replay.test.ts:40` ×2, `unit/exit-codes.test.ts:10` |
| 3 | the engine stopped: no CASE arm holds: evaluating the failure again: no CASE arm holds | `unit/check.test.ts:2407`, `unit/check.test.ts:1521`, `unit/check.test.ts:3055` |
| 3 | the engine stopped: record compared with a function | `unit/engine.test.ts:46` ×3 |
| 3 | the engine stopped: variable not assigned: evaluating the failure again: it didn't fail | `unit/check.test.ts:1854`, `unit/check.test.ts:1859`, `unit/native-search.test.ts:1161` |
| 2 | a constant part of a temporal formula that isn't a boolean | `unit/check.test.ts:5337` ×2 |
| 2 | a value that isn't a set where TLC wants one, which the constant evaluator doesn't compute | `unit/check.test.ts:5562` ×2 |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: a bag that isn't a function | `unit/bags.test.ts:97` ×2 |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: applied a function outside its domain | `unit/check.test.ts:2695`, `unit/check.test.ts:2692` |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: expected a set, not a integer | `unit/check.test.ts:2675` ×2 |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: SubSeq outside the sequence's domain | `unit/check.test.ts:2330` ×2 |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: the builtin \sqsubseteq | `unit/bags.test.ts:97`, `unit/bags.test.ts:107` |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: TLCGet | `unit/tlc-action.test.ts:10`, `unit/tlc-revision.test.ts:26` |
| 2 | an operator, which the constant evaluator doesn't compute | `unit/engine-ir.test.ts:190`, `unit/check.test.ts:5337` |
| 2 | SANY's report of a module-level RECURSIVE declaration that something else binds, or an INSTANCE may: F | `unit/check.test.ts:3442`, `unit/check.test.ts:4626` |
| 2 | the engine declined: the builtin EmptyBag@Bags, whose value the interpreter computes | `unit/modules.test.ts:136` ×2 |
| 2 | the engine declined: unsupported: F | `unit/operator-constants.test.ts:34` ×2 |
| 2 | the engine declined: unsupported: PrintT | `unit/tlc-statistics.test.ts:11`, `unit/tlc-constraint-order.test.ts:11` |
| 2 | the engine stopped: a CASE condition that isn't a boolean: evaluating the failure again: expected a boolean, not a integer | `unit/check.test.ts:2407` ×2 |
| 2 | the engine stopped: a tuple pattern that doesn't match: evaluating the failure again: a tuple pattern that doesn't match | `unit/native-search.test.ts:1388`, `unit/native-search.test.ts:1360` |
| 2 | the engine stopped: an atom of the temporal properties that may fail to evaluate: evaluating the failure again: enumerated an infinite set | `unit/engine.test.ts:1011`, `unit/check.test.ts:2428` |
| 2 | the engine stopped: an IF condition that isn't a boolean: evaluating the failure again: expected a boolean, not a integer | `unit/check.test.ts:2407` ×2 |
| 2 | the engine stopped: an invariant violated | `unit/check.test.ts:644`, `unit/check.test.ts:2521` |
| 2 | the engine stopped: applied a function outside its domain: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/tlc-replay.test.ts:40`, `unit/check.test.ts:1627` |
| 2 | the engine stopped: equality of values TLC can't compare: evaluating the failure again: equality of values TLC can't compare | `unit/check.test.ts:1416` ×2 |
| 2 | the engine stopped: expected a function: evaluating the failure again: a bag that isn't a function | `unit/native-builtins.test.ts:228` ×2 |
| 2 | the engine stopped: Print inside ENABLED | `unit/engine-print.test.ts:31`, `unit/native-search.test.ts:1314` |
| 2 | the engine stopped: printing where the native checker doesn't check the temporal properties: prints it doesn't place in TLC's order | `unit/native-search.test.ts:1074`, `unit/native-search.test.ts:1058` |
| 2 | the engine stopped: TLCExt's Trace, the behavior the engine doesn't keep | `unit/tlc-ext.test.ts:17`, `unit/tlc-ext.test.ts:30` |
| 2 | the engine stopped: ToString of a text the engine made unranked | `unit/native-builtins.test.ts:279`, `unit/native-builtins.test.ts:491` |
| 2 | the engine stopped: unsupported: a state holding a function TLC keeps lazy | `unit/check.test.ts:1963`, `unit/check.test.ts:1934` |
| 2 | the engine stopped: values TLC can't compare: evaluating the failure again: a set TLC leaves unnormalized | `unit/native-builtins.test.ts:228`, `unit/check.test.ts:1675` |
| 2 | the liveness checker declined: an atom the engine doesn't answer | `unit/tlc-live-level.test.ts:18`, `unit/native-search.test.ts:1106` |
| 1 | a CHOOSE no element of which satisfies, which the constant evaluator doesn't compute | `unit/check.test.ts:1290` |
| 1 | a configuration error that shows a value | `unit/check.test.ts:5027` |
| 1 | a configuration substitute with effects, which TLC evaluates at every use: C <- Foo | `unit/check.test.ts:1040` |
| 1 | a temporal property's counterexample: a step back into the cycle of a spec that prints | `unit/counter-example.test.ts:11` |
| 1 | a violating successor TLC fails to find again from its generator | `unit/randomization.test.ts:41` |
| 1 | an ALIAS without a definition | `unit/alias.test.ts:72` |
| 1 | an assumption that fails to evaluate: an assumption the engine found to hold that doesn't again | `unit/check.test.ts:69` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: a bag whose count isn't an integer | `unit/bags.test.ts:107` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: a bag with a count that isn't positive | `unit/bags.test.ts:97` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: a power set too large to build | `unit/check.test.ts:3084` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: a SelectSeq test that isn't a boolean | `unit/check.test.ts:2330` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: evaluating a an unbounded quantifier | `unit/check.test.ts:1473` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: expected a boolean, not a set | `unit/check.test.ts:2675` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: expected a sequence, not "ab" | `unit/check.test.ts:2330` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: expected an integer, not a boolean | `unit/check.test.ts:2330` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: Head of the empty sequence | `unit/check.test.ts:2330` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: JsonDeserialize, whose file the replay doesn't read or write | `unit/json.test.ts:11` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: no CASE arm holds | `unit/check.test.ts:1453` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: recursion too deep | `unit/exit-codes.test.ts:10` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: Tail of the empty sequence | `unit/check.test.ts:2330` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: the builtin BagIn | `unit/bags.test.ts:97` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: the builtin IsABag | `unit/bags.test.ts:120` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: the builtin ToJson | `unit/check.test.ts:761` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: the builtin ToJson@Json | `unit/modules.test.ts:152` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: the builtin Trace | `unit/tlc-ext-operators.test.ts:11` |
| 1 | no step from state N is the trace's next | `unit/check.test.ts:721` |
| 1 | SANY's report of a module nested in another that declares RECURSIVE R | `unit/check.test.ts:4626` |
| 1 | SANY's report of a RECURSIVE declaration of a name a module binds or names before it: F | `unit/check.test.ts:4677` |
| 1 | several states TLC may take for the search's under VIEW or SYMMETRY | `unit/native-search.test.ts:870` |
| 1 | the engine declined: checking an assumption again: an assumption the engine doesn't evaluate that fails to: AssertError of a message that isn't a string | `unit/tlc-ext-operators.test.ts:69` |
| 1 | the engine declined: unsupported: a value TLC computed at startup with effects | `unit/native-search.test.ts:1641` |
| 1 | the engine declined: unsupported: AssertEq | `unit/tlc-ext-operators.test.ts:11` |
| 1 | the engine declined: unsupported: enumerating a lazy set of the state under a VIEW | `unit/check.test.ts:2155` |
| 1 | the engine declined: unsupported: enumerating a set TLC keeps lazy (Alias: UNION at line 5) | `unit/native-sets.test.ts:333` |
| 1 | the engine declined: unsupported: enumerating a set TLC keeps lazy (Product at line 5) | `unit/check.test.ts:5116` |
| 1 | the engine declined: unsupported: enumerating a set TLC keeps lazy (UNION at line 4) | `unit/check.test.ts:5206` |
| 1 | the engine declined: unsupported: expression UnboundedQuantifier | `unit/bundled-modules.test.ts:16` |
| 1 | the engine declined: unsupported: Inc | `unit/operator-constants.test.ts:17` |
| 1 | the engine declined: unsupported: Print where TLC evaluates it otherwise | `unit/native-search.test.ts:1306` |
| 1 | the engine declined: unsupported: RandomElement | `unit/randomization.test.ts:142` |
| 1 | the engine declined: unsupported: TLCGetAndSet | `unit/tlc-ext-operators.test.ts:94` |
| 1 | the engine declined: unsupported: UNCHANGED in the initial predicate | `unit/native-search.test.ts:1396` |
| 1 | the engine declined: unsupported: walking a lazy function over a tuple | `unit/check.test.ts:1830` |
| 1 | the engine stopped: a guard that isn't a boolean: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/check.test.ts:1854` |
| 1 | the engine stopped: a SelectSeq test that isn't a boolean: evaluating the failure again: a SelectSeq test that isn't a boolean | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: a VIEW that fails on an initial state | `unit/engine-symmetry.test.ts:25` |
| 1 | the engine stopped: an atom of the temporal properties that may fail to evaluate: evaluating the failure again: an EvalException adding an initial state | `unit/exit-codes.test.ts:10` |
| 1 | the engine stopped: an atom of the temporal properties that may fail to evaluate: evaluating the failure again: it didn't fail | `unit/engine.test.ts:1011` |
| 1 | the engine stopped: an initial state that isn't complete: evaluating the failure again: an initial state that isn't complete | `unit/exit-codes.test.ts:10` |
| 1 | the engine stopped: an invariant violated: a _POSSIBLE predicate | `unit/possible.test.ts:72` |
| 1 | the engine stopped: an order of model values the search ranked | `unit/native-builtins.test.ts:315` |
| 1 | the engine stopped: an overflow counting the elements of a power set: evaluating the failure again: a state TLC fingerprints only where its constraints hold | `unit/check.test.ts:2121` |
| 1 | the engine stopped: an overflow counting the elements of a power set: evaluating the failure again: an action that fails or prints after a successor TLC can't fingerprint | `unit/check.test.ts:2137` |
| 1 | the engine stopped: applied a function outside its domain: rebuilding a trace: primed variable not assigned: x | `unit/native-search.test.ts:1460` |
| 1 | the engine stopped: applied a non-function: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/check.test.ts:1627` |
| 1 | the engine stopped: BagCardinality of a non-bag: evaluating the failure again: a bag whose count isn't an integer | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: BagCardinality of a non-bag: evaluating the failure again: a bag with a count that isn't positive | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: BagOfAll of a literal | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: CHOOSE found no element: a failure in a model with temporal properties | `unit/tlc-replay.test.ts:40` |
| 1 | the engine stopped: division by zero | `unit/check.test.ts:2508` |
| 1 | the engine stopped: division by zero: a failure in a model with temporal properties | `unit/tlc-replay.test.ts:40` |
| 1 | the engine stopped: division by zero: a failure with a POSTCONDITION | `unit/possible.test.ts:110` |
| 1 | the engine stopped: drew from a set whose shape the engine forgets | `unit/native-builtins.test.ts:417` |
| 1 | the engine stopped: enumerated [D -> R] with R infinite | `unit/native-sets.test.ts:169` |
| 1 | the engine stopped: enumerated a filter of an infinite set: evaluating the failure again: a state whose fingerprint the replay doesn't follow | `unit/check.test.ts:1934` |
| 1 | the engine stopped: enumerated a non-set: a failure in a model with temporal properties | `unit/check.test.ts:2489` |
| 1 | the engine stopped: enumerated a product of an infinite set | `unit/native-sets.test.ts:169` |
| 1 | the engine stopped: enumerated a set TLC can't enumerate: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/native-sets.test.ts:207` |
| 1 | the engine stopped: enumerated an infinite set | `unit/native-sets.test.ts:169` |
| 1 | the engine stopped: enumerated an operation on infinite sets | `unit/bundled-modules.test.ts:23` |
| 1 | the engine stopped: equality of values TLC can't compare: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/check.test.ts:1416` |
| 1 | the engine stopped: equality of values TLC can't compare: evaluating the failure again: the builtin BagIn | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: EXCEPT on a non-function: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/check.test.ts:1627` |
| 1 | the engine stopped: EXCEPT on a non-function: evaluating the failure again: Attempted to apply EXCEPT construct to the value 1. | `unit/check.test.ts:2573` |
| 1 | the engine stopped: EXCEPT outside the domain | `unit/check.test.ts:1627` |
| 1 | the engine stopped: expected a bag: evaluating the failure again: it didn't fail | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: expected a boolean: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/native-sets.test.ts:169` |
| 1 | the engine stopped: expected a function: evaluating the failure again: the builtin \sqsubseteq | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: expected a function: evaluating the failure again: the builtin BagIn | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: expected a function: evaluating the failure again: the builtin BagOfAll | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: expected a function: evaluating the failure again: the builtin SubBag | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: expected a sequence: evaluating the failure again: expected a sequence, not "ab" | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: expected a set: evaluating the failure again: expected a set, not a function | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: expected an integer: evaluating the failure again: a bag whose count isn't an integer | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: expected an integer: evaluating the failure again: the builtin CopiesIn | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: expected an integer: evaluating the failure again: the builtin SortSeq | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: expected an integer: evaluating the failure again: the builtin SubBag | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: printing where the native checker doesn't check the temporal properties: a node that accepts every behavior | `unit/native-search.test.ts:1046` |
| 1 | the engine stopped: printing where the native checker doesn't check the temporal properties: a predicate the engine leaves to the interpreter | `unit/check.test.ts:2466` |
| 1 | the engine stopped: printing where the native checker doesn't check the temporal properties: steps from states it didn't store | `unit/native-search.test.ts:826` |
| 1 | the engine stopped: quantified over a non-set: evaluating the failure again: expected a set, not a integer | `unit/native-search.test.ts:505` |
| 1 | the engine stopped: RandomSubset of a product too large to index | `unit/native-builtins.test.ts:390` |
| 1 | the engine stopped: RandomSubset of an interval too large to draw from | `unit/native-builtins.test.ts:401` |
| 1 | the engine stopped: SortSeq of a non-sequence: evaluating the failure again: the builtin SortSeq | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: SubBag of a non-bag: evaluating the failure again: the builtin SubBag | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: SubSeq of a non-sequence: evaluating the failure again: expected a sequence, not {1} | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: TLCGet of a key that isn't a natural number | `unit/check.test.ts:2837` |
| 1 | the engine stopped: TLCGet of a register TLC hasn't set | `unit/check.test.ts:2837` |
| 1 | the engine stopped: TLCModelValue of a value that isn't a string: evaluating the failure again: TLCModelValue of a value that isn't a string | `unit/native-builtins.test.ts:334` |
| 1 | the engine stopped: unsupported: TLCGet("diameter") in the search | `unit/check.test.ts:248` |
| 1 | the engine stopped: unsupported: TLCSet of a key that stops or configures TLC | `unit/tlc-pause.test.ts:8` |
| 1 | the liveness checker declined: a late node TLC adds at another diameter | `unit/native-search.test.ts:1103` |
| 1 | TLCGet, which the constant evaluator doesn't compute | `unit/check.test.ts:1034` |

### What uses it as the reference, and what replaces it

| User | Replacement |
|---|---|
| Unit tests of the interpreter's internals (about 30 cases) | Deleted with the code; `enumeration-oracle` keeps native against TLC's frozen answers; `engine-store` and `engine-fingerprints` check the native store against `ValueOracle` |
| Unit tests that compare the engine with the interpreter (about 200 cases: `native-search`, `native-sets`, `native-builtins`, `engine*`, the `PROVE_IT_ENGINE=0` runs in `check` and `cli`) | Golden output recorded once from TLC at d8fb231, as the existing fixture `.out` files are; `compareStateLogs` becomes 1 thread against 4 plus TLC's counts |
| `differential.ts` pairs `rust/interpreter` and `rust/stopped` | Gone with the hand-over they test; `tlc/rust` and `tlc/native` against `tlc-stdout` stay |
| `engine-coverage.ts`'s run with the engine off | Dropped; `expected.json` judges the outcome |
| `value-oracle.ts`'s interpreter fingerprints and TypeScript store | Dropped; TLC's classes stay the oracle |
| `front-differential.ts`'s TypeScript side | Goes with the TypeScript front end |
| Verification's Packages and Binary checks with `PROVE_IT_ENGINE=0` | Checks of the WebAssembly engine in `dist` |

The 39 passing models TLC takes more than 20 s on have outcome recordings in `expected.json` but
no full `tlc-stdout`. Recording them is deferred.

### Stages

- **S0. The front end.** `tla-front` replaces the TypeScript SANY front end and `ir.ts` in the
  library, and the addon and the WebAssembly module take module sources through a loader callback.
  This is the front end's workstream.
- **S1. The binary's check as a host entry.** First, as a pure refactor, `prove-it-cli`'s check
  driver moves into a crate the binary and `prove-it-host` share. `tla-trace` and `tla-live` print
  through a sink, not stdout, and the driver returns a structured outcome (status, counts,
  violation, trace states) beside the lines. The binary must stay byte-identical. Then
  `check_sources` takes sources through S0's loader. `native.ts` and `wasm.ts` call it, and the
  library flips once `tlc/rust` equals `tlc/native` on all 1466 runs. That removes the 15 declines
  and the 131 hand-overs together.
- **S2. The interpreter-only features, built natively:** `-dump` (which `state-graph`'s tests also
  need), `-continue`, periodic configs and TLC 1.7.4's output, each after measuring how often the
  tests and the corpus use it; and `tla-live`'s declines, where a test or a model meets one. For
  WebAssembly's stack, measure how many corpus models trap now, then choose a larger stack or
  iterative recursion.
- **S3. Tests on TLC's recordings,** recorded once with a recorder script.
- **S4. Flip and delete.**
  - `check` loses the interpreter tier, `PROVE_IT_ENGINE=0` and `PROVE_IT_LIVE_CHECK`.
  - About 24,000 lines go: `evaluate`, `values`, `environment`, `successors`, `search`, the
    interpreter's part of `check`, `liveness*`, `tableau`, `state-graph`, `builtins`, `bags`,
    `java-overrides`, `parallel*`, `worker`, `fingerprints`, `symmetry`, `randomization`,
    `transfer`, `dependencies`, `codegen`, `runtime`, `instances`, `subexpressions`,
    `spec-description`, the rest of `tlc/`, and `engine/store`, `convert`, `fingerprint`,
    `native-store` and `ir`.

### The public API afterwards

`check` and its option, progress, result and status types, `prove` and its types, `parseConfig`,
and the errors stay. `parseModule` and `Module` are the front end's to decide.

`Value`, `formatValue` and the values in `TraceStep` and `Violation` are the interpreter's classes.
The proposal: a trace step carries each variable as TLC prints it, from the native printer, and as
plain decoded data with no classes. `formatValue` is dropped, or becomes a thin native printer if a
caller needs one. This breaks callers that hold `Value`s, so it waits for the owner. The exports
don't change until then.

### What changes for users

- `PROVE_IT_ENGINE=0` goes. Where no engine loads, `EngineUnavailableError` has no escape hatch:
  - WebAssembly fails to compile;
  - or `dist` lacks the engine.
  A browser keeps the WebAssembly engine.
- A WebAssembly stack overflow becomes an error unless S2 lifts it first.
- `-dump`, `-continue`, periodic configs and TLC 1.7.4 are checked natively.
- The library prints what the binary prints. Today they differ only where the library hands over.
