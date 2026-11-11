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

Neither side implements `-simulate`, `-generate`, `-debug` or `-loadTrace`. The binary writes
`-dumpTrace tlc` and `-dumpTrace json`, and declines the other formats and the cases cli.md's
"-dumpTrace" lists; the interpreter writes none.
`src/pcal` only validates for SANY, `src/obligations` imports nothing from the interpreter, and
`src/prover` imports only `worker.ts`'s thread helpers (`isWorkerSupported`, `spawnWorker`,
`getParentPort`). Those move to the prover. `tlc/version.ts`, `tlc/jar-data.ts` and
`tlc/messages.ts` are shared with the front end and the CLI, so they move too.

### Every `check` of the library's tests, through the binary

`bun scripts/run.ts check-log` measures this; it is the retirement's progress meter. It runs
`bun test` with `PROVE_IT_CHECK_LOG`, under which each `check` given its configuration as text writes
its source, configuration, options and calling test, and each module, override class and file it
reads. Then it runs each distinct check through the binary with TLC's command line for its options.
Each check runs on one thread and with every level shared between four, and once more on one thread
without `-noGenerateSpecTE`, as TLC runs by default. A run a signal ends counts as not native.
`--json` writes each check with its answers.

What changes what a check does, and whether the meter keeps it. A setting it keeps is logged, part
of the key that makes two checks one, and given to the binary:

- Kept: the source and configuration, which hold `CHECK_DEADLOCK` and the constraints; the modules,
  override classes and files the check reads (a file the check reads by an absolute path, or outside
  its directory, the binary reads where the test left it); the seed; `-lncheck`; `-workers`; `-tool`;
  `-nowarning`; `-dump` with its format; `-continue`; TLC 1.7.4; the Java system properties `TLCGet`
  reads; and `PROVE_IT_TEST_LIVE_CHECK_AT`, which has the search check the temporal properties at a
  state.
- Fixed by the meter: `-fp 0`, the only fingerprint the library takes; and `PROVE_IT_WORKERS` and
  `PROVE_IT_SHARED_LEVEL`, since the meter runs every check on one thread and on four with every
  level shared.
- Not kept, on purpose:
  - `PROVE_IT_ENGINE`, which turns the engine off or reports what it did, and `PROVE_IT_STOP_AT`,
    which stops the engine's search to make the library fall back. The meter asks whether the binary
    checks the model, whatever the library did with it.
  - The self-checks `PROVE_IT_LIVE_CHECK`, `PROVE_IT_FINGERPRINT`, `PROVE_IT_FP_VERIFY`,
    `PROVE_IT_EPOCH_CHECK` and `PROVE_IT_MEMO=off`. Each computes an answer another way and fails
    where the two disagree, without changing it, and the binary reads none of them.
  - `PROVE_IT_STATE_LOG`, which only writes the states found, and `PROVE_IT_TEST_IR`, which only the
    binary's own tests set.
  - Whether the caller printed SANY's report, which the binary always prints, and whether TLC records
    a trace, which the default-mode run covers.
  - A configuration given as an object, as by the command line with `-deadlock`. The binary's tests
    and the differentials run that command line.

Measured at main 6871cd2, with the log as this section gives it:

- 1,885 checks. 1,218 print TLC's output natively. Their exit codes are 0 (559), 150 (168), 12
  (103), 10 (94), 75 (93), 13 (81), 151 (52), 255 (29), 11 (13), 14 (11), 76 (9) and 77 (6).
- 667 are `not native yet`, for 206 reasons, grouped below and listed in full after.
- One thread and four gave the same answer for every check.
- In TLC's default mode, which generates the trace exploration spec (the same checks without
  `-noGenerateSpecTE`), 245 are native. 1,412 decline as "SANY's report of the trace exploration
  spec TLC parses with the spec".
- None used `-continue`.

| Kind | Runs | Reasons | Test files (runs) |
|---|---:|---:|---|
| The command line (`-dump`, TLC 1.7.4) | 168 | 2 | `native-sets` 58, `check` 50, `native-search` 23, `native-builtins` 15, `state-graph` 11, `tlc-replay` 5 … |
| Rebuilding a run-time failure | 161 | 60 | `check` 58, `engine` 49, `native-builtins` 29, `native-search` 8, `operator-constants` 4, `tlc-replay` 4 … |
| Rebuilding a failing assumption | 94 | 38 | `check` 70, `bags` 18, `json` 1, `exit-codes` 1, `tlc-ext-operators` 1, `tlc-revision` 1 … |
| The engine stops the search | 86 | 34 | `check` 31, `native-builtins` 17, `engine` 8, `exit-codes` 6, `native-search` 5, `tlc-replay` 4 … |
| The engine declines the model | 50 | 23 | `check` 12, `native-search` 11, `native-sets` 7, `tlc-ext-operators` 6, `engine-print` 4, `operator-constants` 3 … |
| Front end, configuration and printing | 44 | 22 | `check` 13, `overrides` 10, `engine-print` 5, `alias` 4, `printing` 3, `possible` 3 … |
| Temporal properties | 40 | 20 | `check` 12, `native-search` 8, `tlc-replay` 4, `tlc-live-level` 4, `temporal` 3, `engine` 3 … |
| Constant evaluation | 24 | 7 | `check` 10, `engine` 5, `exit-codes` 2, `bags` 2, `engine-print` 1, `instances` 1 … |

#### Liveness

Measured again at main 33b0d56, after #217, #239, #244, #253, #265 and #277, with `check-log`
counting TLC 1.7.4's checks apart (63, retired with the interpreter): 286 of the other checks have
temporal properties, 232 are native and 54 are not. 22 of those 54 are the liveness part of this
plan, down from 43:
- a failure in a model with temporal properties: an atom of the temporal properties that may fail
  to evaluate (2), and SUBSET of a non-set evaluated again after Next fails (1);
- the search's stops in a model with temporal properties: deadlock (3), an invariant (1), a
  division by zero (1). Two of the deadlocks, `tlc-replay`'s, are native now: TLC prints the call
  stack of the check that fails as it adds the deadlocked state to the behavior graphs
  ([liveness.md](liveness.md)). The third prints in Next, which TLC runs again for a late node;
- a property TLC finds a tautology (3), or a constant part of a temporal formula that isn't a
  boolean (2);
- printing where the native checker doesn't check the temporal properties (5): prints it doesn't
  place in TLC's order (2), a node that accepts every behavior, a predicate the engine leaves to the
  interpreter, and steps from states it didn't store (1 each);
- an atom the engine doesn't answer, a late node at another diameter, a step back into the cycle of
  a spec that prints, and several states under VIEW or SYMMETRY (1 each).

Of the other 32: constant evaluation (9), a constraint, a VIEW or an action property that fails on
a successor (8), a power set too large to build (3), `-dump` (3), the builtin Trace and PrintT
(2 each), and five more of the evaluator's and the front end's gaps (1 each).

The corpus has no temporal decline: `differential --native-only` matches 1,460 of 1,466 runs, and
the 6 known differences aren't about liveness.

A lasso that ends in the first state of its cycle (the `temporal` test's three runs) is a printing
gap. TLC prints every state, then stutters at the cycle's first state, and so does the binary now.
A grid of 160 small specs (`prove-it-cli/tests/lasso-grid`) prints what TLC prints on all 640 runs:
one thread and four, checking the properties periodically and at the end.

A property TLC finds a tautology, and a constant part of a temporal formula that isn't a boolean,
are native. TLC stops at a property's \A over the empty set as it unrolls the properties
(`SpecProcessor.processConfigProps`), and at a formula whose negation has no solution
(`ModelChecker.modelCheckImpl`), with `EC.TLC_LIVE_FORMULA_TAUTOLOGY`. It stops at a constant part
of a temporal formula whose value isn't a boolean (`Liveness.astToLive`) with
`EC.TLC_EXPECTED_VALUE`, which names the part by `SemanticNode.toString`: a numeral's image, such
as `\b101`, or else the part's location. A grid of 64 small specs
(`prove-it-cli/tests/live-startup-grid`) prints what TLC prints on 488 of its 512 runs, and the
other 24 decline for the constant evaluator's gaps.

Nothing reaches these liveness declines, so they stay declines until a test or a model does:
- an accepting node under SYMMETRY or a VIEW;
- an unexpanded graph;
- uncounted branches;
- every decline of atoms that read or set TLC's registers.

#### Declines to win back

A correctness fix can turn a run that matched TLC into a decline, where the engine can't yet tell
it from one that printed something else. Each is outside the corpus:
- a function constructor that binds a tuple pattern over a set of functions TLC built as
  functions, applied at once (`[<<a, b>> \in {[k \in 1..2 |-> k]} |-> a][<<1, 2>>]`). TLC applies
  the function without building it, so it never binds the pattern; the engine builds it and
  declines the binding, since `ContextEnumerator` binds a tuple pattern only to a `TupleValue`
  (#245).
- a lazy set streamed where TLC may have normalized the object it streams, whose stream differs
  from the normalized set only where nothing printed depends on it (`lazy-duplicates.md`): an
  invariant violated before the stream first differs, or a stream whose order alone differs
  where the first initial state to violate an invariant is the same in either order. Nine cells
  of `prove-it-cli/tests/lazy_duplicates.rs` printed what TLC prints so before and decline now:
  `kept.cupOrder.{constVar, ex1, letEval, opAfter, varPlain}.init` and
  `kept.unionSub.{constHeld, constSized, constEqual, constCup}`. To win them back, decline at the
  first position where the stream differs from the normalized set, not where the stream starts.

#### Known wrong outputs

These print a "states generated" other than TLC's today, outside the corpus and the tests; why,
with TLC's source, is in [lazy-duplicates.md](lazy-duplicates.md):

| Shape | Repro | TLC | Native |
|---|---|---:|---:|
| A held SUBSET or set of functions `\cup` a set that overlaps it | `Init == s = 0 /\ x = 0`, `Next == s' = SUBSET {1} /\ x' \in s' \cup {{1}}` | 10 | 7 |

The engine now declines the shapes that printed other counts here too: a constant definition
normalized elsewhere, then streamed (`C == UNION {1..2, 2..3}`, `Init == s = C /\ x = 0`,
`Next == s' = s /\ x' \in C`: TLC 13, native 17), a stream whose order alone differs from the
normalized set's (`(SUBSET {2}) \cup {{1}}` through a variable, a constant via a variable, a `\E`
name or a LET named twice), and a variable bound by `\in` to a set enumeration's lazy first
element (`Next == s' \in {UNION {1..2, 2..3}} /\ y' \in s'`: TLC 17, native 13).

#### Every reason

Measured with `bun scripts/run.ts check-log` at #272 (main 924d7cd merged), so the counts follow
"After the FingerprintException burn-down" below, not the measurement above.

| Runs | Reason | Tests |
|---:|---|---|
| 63 | TLC 1.7.4 | `unit/check.test.ts:2573` ×5, `unit/check.test.ts:5133` ×3, `unit/check.test.ts:129` ×3, `unit/check.test.ts:1353` ×2, `unit/check.test.ts:2521` ×2, `unit/check.test.ts:5579` ×2, `unit/state-graph.test.ts:22` ×2, `unit/check.test.ts:5498` ×2, `unit/tlc-replay.test.ts:40` ×2, `unit/check.test.ts:2466`, `unit/check.test.ts:3519`, `unit/modules.test.ts:157`, `unit/check.test.ts:111`, `unit/check.test.ts:5541`, `unit/check.test.ts:1485`, `unit/liveness.test.ts:108`, `unit/modules.test.ts:152`, `unit/check.test.ts:5276`, `unit/check.test.ts:2508`, `unit/check.test.ts:2035`, `unit/check.test.ts:5363`, `unit/check.test.ts:1329`, `unit/check.test.ts:5440`, `unit/parallel.test.ts:18`, `unit/check.test.ts:5387`, `unit/check.test.ts:5293`, `unit/tlc-replay.test.ts:225`, `unit/check.test.ts:5416`, `unit/check.test.ts:5251`, `unit/check.test.ts:5468`, `unit/check.test.ts:5371`, `unit/check.test.ts:5256`, `unit/liveness.test.ts:122`, `unit/check.test.ts:5431`, `unit/check.test.ts:5401`, `unit/check.test.ts:5326`, `unit/check.test.ts:5482`, `unit/check.test.ts:5333`, `unit/check.test.ts:5283`, `unit/check.test.ts:2046`, `unit/tlc-replay.test.ts:185`, `unit/randomization.test.ts:162`, `unit/check.test.ts:5264`, `unit/check.test.ts:5424`, `unit/check.test.ts:2339`, `unit/check.test.ts:5454`, `unit/check.test.ts:1980`, `unit/tlc-replay.test.ts:167`, `unit/check.test.ts:5378` |
| 39 | dumping a value whose text depends on how TLC built it | `unit/native-sets.test.ts:86` ×38, `unit/native-builtins.test.ts:222` |
| 14 | the engine stopped: a constraint, a VIEW or an action property that fails on a successor | `unit/exit-codes.test.ts:10` ×3, `unit/tlc-replay.test.ts:40` ×2, `unit/check.test.ts:2983` ×2, `unit/check.test.ts:2071`, `unit/possible.test.ts:110`, `unit/check.test.ts:2013`, `unit/check.test.ts:2081`, `unit/check.test.ts:2026`, `unit/check.test.ts:2046`, `unit/check.test.ts:2002` |
| 11 | a constant invariant the engine checks, which TLC may warn about | `unit/engine.test.ts:46` ×3, `unit/engine.test.ts:807` ×2, `unit/bags.test.ts:43` ×2, `unit/exit-codes.test.ts:10`, `unit/engine-print.test.ts:31`, `unit/instances.test.ts:43`, `unit/tlc-replay.test.ts:197` |
| 11 | the engine declined: unsupported: Print | `unit/native-search.test.ts:1307` ×7, `unit/engine-print.test.ts:31` ×4 |
| 9 | an assumption that fails to evaluate: evaluating the assumption again: expected an integer, not a string | `unit/check.test.ts:3159` ×4, `unit/check.test.ts:2330` ×4, `unit/check.test.ts:2593` |
| 8 | -dump dot | `unit/state-graph.test.ts:22` ×8 |
| 6 | the engine stopped: a power set too large to build | `unit/engine.test.ts:1149` ×4, `unit/engine-print.test.ts:31`, `unit/engine.test.ts:680` |
| 5 | a POSTCONDITION or an ALIAS TLC may compute as it starts | `unit/alias.test.ts:72` ×2, `unit/possible.test.ts:123`, `unit/alias.test.ts:89`, `unit/possible.test.ts:118` |
| 5 | an assumption that fails to evaluate: evaluating the assumption again: integer overflow | `unit/check.test.ts:2330` ×5 |
| 5 | an assumption that fails to evaluate: evaluating the assumption again: SUBSET of a non-set | `unit/check.test.ts:2330` ×4, `unit/check.test.ts:2583` |
| 5 | the engine stopped: enumerated Nat | `unit/check.test.ts:3101` ×2, `unit/check.test.ts:1934` ×2, `unit/check.test.ts:1951` |
| 4 | a _POSSIBLE predicate the search didn't witness | `unit/check.test.ts:282`, `unit/possible.test.ts:66`, `unit/native-search.test.ts:1548`, `unit/native-search.test.ts:1541` |
| 4 | an assumption that fails to evaluate: evaluating the assumption again: expected an integer, not a set | `unit/check.test.ts:2330` ×4 |
| 4 | an assumption that fails to evaluate: evaluating the assumption again: it didn't fail | `unit/check.test.ts:2717`, `unit/check.test.ts:2330`, `unit/check.test.ts:2760`, `unit/check.test.ts:2754` |
| 4 | rebuilding a trace: the builtin Trace | `unit/alias.test.ts:48`, `unit/tlc-ext.test.ts:23`, `unit/alias.test.ts:59`, `unit/alias.test.ts:28` |
| 4 | the engine declined: unsupported: enumerating a set TLC keeps lazy (UNION at line 3) | `unit/native-sets.test.ts:269` ×3, `unit/native-sets.test.ts:332` |
| 4 | the engine stopped: division by zero: evaluating the failure again: the body of a function TLC keeps lazy | `unit/check.test.ts:1797`, `unit/check.test.ts:1809`, `unit/check.test.ts:1991`, `unit/check.test.ts:1980` |
| 4 | the engine stopped: recursion too deep | `unit/exit-codes.test.ts:10` ×3, `unit/check.test.ts:2928` |
| 4 | the engine stopped: unsupported: comparing a function TLC keeps lazy | `unit/native-search.test.ts:505` ×3, `unit/native-builtins.test.ts:228` |
| 4 | the engine stopped: unsupported: TLCGet of a key the search doesn't keep | `unit/tlc-statistics.test.ts:25`, `unit/check.test.ts:248`, `unit/check.test.ts:2837`, `unit/check.test.ts:5387` |
| 4 | values TLC can't compare, which the constant evaluator doesn't compute | `unit/check.test.ts:1257` ×3, `unit/exit-codes.test.ts:10` |
| 3 | -dump under SYMMETRY or a VIEW | `unit/native-search.test.ts:607`, `unit/native-search.test.ts:603`, `unit/native-search.test.ts:542` |
| 3 | a constant definition the configuration names | `unit/check.test.ts:5036`, `unit/check.test.ts:5028`, `unit/check.test.ts:5031` |
| 3 | a division by zero, which the constant evaluator doesn't compute | `unit/check.test.ts:5524`, `unit/check.test.ts:1300`, `unit/liveness.test.ts:122` |
| 3 | a property TLC finds a tautology | `unit/check.test.ts:5333`, `unit/check.test.ts:5211`, `unit/check.test.ts:5541` |
| 3 | a SYMMETRY definition that isn't an operator applied to its sets | `unit/check.test.ts:1243` ×2, `unit/exit-codes.test.ts:10` |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: expected a sequence, not 1 | `unit/check.test.ts:2330` ×2, `unit/check.test.ts:2339` |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: expected an integer, not a function | `unit/check.test.ts:2330` ×3 |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: the builtin AssertEq | `unit/check.test.ts:770` ×2, `unit/json.test.ts:11` |
| 3 | printing a value whose text depends on how TLC built it | `unit/printing.test.ts:7` ×3 |
| 3 | temporal quantification in the specification | `unit/specifications.test.ts:68` ×2, `unit/exit-codes.test.ts:10` |
| 3 | the engine declined: unsupported: PickSuccessor | `unit/tlc-ext-operators.test.ts:11` ×2, `unit/tlc-ext-operators.test.ts:61` |
| 3 | the engine stopped: an order of strings the search ranked | `unit/native-builtins.test.ts:279` ×2, `unit/native-builtins.test.ts:327` |
| 3 | the engine stopped: applied a function outside its domain: evaluating the failure again: applied a function outside its domain | `unit/check.test.ts:1896`, `unit/check.test.ts:1874`, `unit/native-search.test.ts:505` |
| 1 | the engine stopped: deadlock | `unit/check.test.ts:2521` |
| 3 | the engine stopped: expected an integer: evaluating the failure again: expected an integer, not a string | `unit/tlc-replay.test.ts:40` ×2, `unit/exit-codes.test.ts:10` |
| 3 | the engine stopped: record compared with a function | `unit/engine.test.ts:46` ×3 |
| 2 | a constant part of a temporal formula that isn't a boolean | `unit/check.test.ts:5354` ×2 |
| 2 | a Java override that computes its value | `unit/overrides.test.ts:96`, `unit/overrides.test.ts:82` |
| 2 | a value that isn't a set where TLC wants one, which the constant evaluator doesn't compute | `unit/check.test.ts:5579` ×2 |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: applied a function outside its domain | `unit/check.test.ts:2692`, `unit/check.test.ts:2695` |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: SubBag's >=, which may be Naturals' or Integers' | `unit/bags.test.ts:97`, `unit/check.test.ts:501` |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: TLCGet | `unit/tlc-revision.test.ts:26`, `unit/tlc-action.test.ts:10` |
| 2 | an operator, which the constant evaluator doesn't compute | `unit/check.test.ts:5354`, `unit/engine-ir.test.ts:190` |
| 2 | SANY's report of a module-level RECURSIVE declaration that something else binds, or an INSTANCE may: F | `unit/check.test.ts:4626`, `unit/check.test.ts:3442` |
| 2 | the engine declined: the builtin EmptyBag@Bags, whose value the interpreter computes | `unit/modules.test.ts:136` ×2 |
| 2 | the engine declined: unsupported: enumerating a set TLC keeps lazy (UNION at line 5) | `unit/native-sets.test.ts:343`, `unit/check.test.ts:1606` |
| 2 | the engine declined: unsupported: F | `unit/operator-constants.test.ts:34` ×2 |
| 2 | the engine declined: unsupported: PrintT | `unit/tlc-constraint-order.test.ts:11`, `unit/tlc-statistics.test.ts:11` |
| 2 | the engine stopped: a guard that isn't a boolean: evaluating the failure again: a next-state relation the IR holds no actions of | `unit/exit-codes.test.ts:10`, `unit/check.test.ts:2961` |
| 2 | the engine stopped: an invariant violated | `unit/check.test.ts:644`, `unit/check.test.ts:2521` |
| 2 | the engine stopped: equality of values TLC can't compare: evaluating the failure again: equality of values TLC can't compare | `unit/check.test.ts:1416` ×2 |
| 2 | the engine stopped: Print inside ENABLED | `unit/engine-print.test.ts:31`, `unit/native-search.test.ts:1315` |
| 2 | the engine stopped: printing where the native checker doesn't check the temporal properties: prints it doesn't place in TLC's order | `unit/native-search.test.ts:1059`, `unit/native-search.test.ts:1075` |
| 2 | the engine stopped: TLCExt's Trace, the behavior the engine doesn't keep | `unit/tlc-ext.test.ts:17`, `unit/tlc-ext.test.ts:30` |
| 2 | the engine stopped: ToString of a text the engine made unranked | `unit/native-builtins.test.ts:491`, `unit/native-builtins.test.ts:279` |
| 2 | the engine stopped: unsupported: a state holding a function TLC keeps lazy | `unit/check.test.ts:1963`, `unit/check.test.ts:1934` |
| 2 | the engine stopped: values TLC can't compare: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/check.test.ts:1675` ×2 |
| 2 | the Java overrides TLC lists in the JVM's order | `unit/engine-ir.test.ts:144`, `unit/overrides.test.ts:16` |
| 1 | -dump with temporal properties | `unit/native-search.test.ts:711` |
| 1 | a CHOOSE no element of which satisfies, which the constant evaluator doesn't compute | `unit/check.test.ts:1290` |
| 1 | a configuration error that shows a value | `unit/check.test.ts:5044` |
| 1 | a configuration substitute with effects, which TLC evaluates at every use: C <- Foo | `unit/check.test.ts:1040` |
| 1 | a Java override class with a static initializer | `unit/overrides.test.ts:82` |
| 1 | a Java override class with a superclass | `unit/overrides.test.ts:82` |
| 1 | a Java override class with annotations | `unit/overrides.test.ts:82` |
| 1 | a Java override class with fields | `unit/overrides.test.ts:82` |
| 1 | a Java override class with methods of one name | `unit/overrides.test.ts:82` |
| 1 | a Java override of a name TLC maps to an operator's | `unit/overrides.test.ts:82` |
| 1 | a Java override with parameters, whose arguments TLC evaluates | `unit/overrides.test.ts:59` |
| 1 | a temporal property's counterexample: a step back into the cycle of a spec that prints | `unit/counter-example.test.ts:11` |
| 1 | a violating successor TLC fails to find again from its generator | `unit/randomization.test.ts:41` |
| 1 | an ALIAS without a definition | `unit/alias.test.ts:72` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: a power set too large to build | `unit/check.test.ts:3084` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: a SelectSeq test that isn't a boolean | `unit/check.test.ts:2330` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: enumerated an infinite set | `unit/check.test.ts:2675` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: evaluating a an unbounded quantifier | `unit/check.test.ts:1473` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: expected a boolean, not a set | `unit/check.test.ts:2675` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: expected a sequence, not "ab" | `unit/check.test.ts:2330` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: expected a set, not a integer | `unit/check.test.ts:2675` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: expected an integer, not a boolean | `unit/check.test.ts:2330` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: recursion too deep | `unit/exit-codes.test.ts:10` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: the builtin ToJson | `unit/check.test.ts:761` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: the builtin ToJson@Json | `unit/modules.test.ts:152` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: the builtin Trace | `unit/tlc-ext-operators.test.ts:11` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: values TLC can't compare | `unit/check.test.ts:3248` |
| 1 | no step from state N is the trace's next | `unit/check.test.ts:721` |
| 1 | SANY's report of a module nested in another that declares RECURSIVE R | `unit/check.test.ts:4626` |
| 1 | SANY's report of a RECURSIVE declaration of a name a module binds or names before it: F | `unit/check.test.ts:4677` |
| 1 | several states TLC may take for the search's under VIEW or SYMMETRY | `unit/native-search.test.ts:870` |
| 1 | the engine declined: checking an assumption again: an assumption the engine doesn't evaluate that fails to: AssertError of a message that isn't a string | `unit/tlc-ext-operators.test.ts:69` |
| 1 | the engine declined: checking an assumption again: an assumption the engine found to hold that doesn't again | `unit/json.test.ts:11` |
| 1 | the engine declined: record compared with a function | `unit/native-search.test.ts:1520` |
| 1 | the engine declined: unsupported: a value TLC computed at startup with effects | `unit/native-search.test.ts:1642` |
| 1 | the engine declined: unsupported: AssertEq | `unit/tlc-ext-operators.test.ts:11` |
| 1 | the engine declined: unsupported: enumerating a lazy set of the state under a VIEW | `unit/check.test.ts:2155` |
| 1 | the engine declined: unsupported: enumerating a set TLC keeps lazy (Alias: UNION at line 5) | `unit/native-sets.test.ts:354` |
| 1 | the engine declined: unsupported: expression UnboundedQuantifier | `unit/bundled-modules.test.ts:16` |
| 1 | the engine declined: unsupported: Inc | `unit/operator-constants.test.ts:17` |
| 1 | the engine declined: unsupported: Print where TLC evaluates it otherwise | `unit/native-search.test.ts:1307` |
| 1 | the engine declined: unsupported: RandomElement | `unit/randomization.test.ts:142` |
| 1 | the engine declined: unsupported: TLCGetAndSet | `unit/tlc-ext-operators.test.ts:94` |
| 1 | the engine declined: unsupported: UNCHANGED in the initial predicate | `unit/native-search.test.ts:1397` |
| 1 | the engine declined: unsupported: walking a lazy function over a tuple | `unit/check.test.ts:1830` |
| 1 | the engine stopped: a conjunct that isn't a boolean: evaluating the failure again: expected a boolean, not a integer | `unit/check.test.ts:2368` |
| 1 | the engine stopped: a tuple pattern that doesn't match: evaluating the failure again: a tuple pattern that doesn't match | `unit/native-search.test.ts:1361` |
| 1 | the engine stopped: a VIEW that fails on an initial state | `unit/engine-symmetry.test.ts:25` |
| 1 | the engine stopped: an atom of the temporal properties that may fail to evaluate | `unit/engine.test.ts:1149` |
| 1 | the engine stopped: an invariant violated: a _POSSIBLE predicate | `unit/possible.test.ts:72` |
| 1 | the engine stopped: an order of model values the search ranked | `unit/native-builtins.test.ts:315` |
| 1 | the engine stopped: an overflow counting the elements of a power set: evaluating the failure again: an action that fails or prints after a successor TLC can't fingerprint | `unit/check.test.ts:2137` |
| 1 | the engine stopped: an overflow counting the elements of a power set: evaluating the failure again: it didn't fail | `unit/check.test.ts:2121` |
| 1 | the engine stopped: applied a function outside its domain: evaluating the failure again: values TLC can't compare | `unit/check.test.ts:2573` |
| 1 | the engine stopped: applied a function outside its domain: rebuilding a trace: primed variable not assigned: x | `unit/native-search.test.ts:1461` |
| 1 | the engine stopped: applied a non-function: evaluating the failure again: applied a non-function: {1, 2} | `unit/check.test.ts:1627` |
| 1 | the engine stopped: BagOfAll of a literal | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: CHOOSE found no element: a failure in a model with temporal properties | `unit/tlc-replay.test.ts:40` |
| 1 | the engine stopped: division by zero | `unit/check.test.ts:2508` |
| 1 | the engine stopped: division by zero: a failure in a model with temporal properties | `unit/tlc-replay.test.ts:40` |
| 1 | the engine stopped: division by zero: a failure with a POSTCONDITION | `unit/possible.test.ts:110` |
| 1 | the engine stopped: drew from a set whose shape the engine forgets | `unit/native-builtins.test.ts:417` |
| 1 | the engine stopped: enumerated [D -> R] with R infinite | `unit/native-sets.test.ts:169` |
| 1 | the engine stopped: enumerated a non-set: a failure in a model with temporal properties | `unit/check.test.ts:2489` |
| 1 | the engine stopped: enumerated a product of an infinite set | `unit/native-sets.test.ts:169` |
| 1 | the engine stopped: enumerated an infinite set | `unit/native-sets.test.ts:169` |
| 1 | the engine stopped: enumerated an operation on infinite sets | `unit/bundled-modules.test.ts:23` |
| 1 | the engine stopped: equality of values TLC can't compare: evaluating the failure again: a failure TLC reports as a FingerprintException | `unit/check.test.ts:1416` |
| 1 | the engine stopped: EXCEPT outside the domain | `unit/check.test.ts:1627` |
| 1 | the engine stopped: expected a boolean: evaluating the failure again: enumerated a lazy filter | `unit/native-sets.test.ts:169` |
| 1 | the engine stopped: expected a boolean: evaluating the failure again: expected a boolean, not a function | `unit/check.test.ts:1403` |
| 1 | the engine stopped: expected a function: evaluating the failure again: BagIn of a value that isn't a function | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: expected a function: evaluating the failure again: SubBag of a value that isn't a function | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: expected an integer: evaluating the failure again: SubBag's >=, which may be Naturals' or Integers' | `unit/native-builtins.test.ts:228` |
| 1 | the engine stopped: printing where the native checker doesn't check the temporal properties: a node that accepts every behavior | `unit/native-search.test.ts:1047` |
| 1 | the engine stopped: printing where the native checker doesn't check the temporal properties: a predicate the engine leaves to the interpreter | `unit/check.test.ts:2466` |
| 1 | the engine stopped: printing where the native checker doesn't check the temporal properties: steps from states it didn't store | `unit/native-search.test.ts:826` |
| 1 | the engine stopped: RandomSubset of a product too large to index | `unit/native-builtins.test.ts:390` |
| 1 | the engine stopped: RandomSubset of an interval too large to draw from | `unit/native-builtins.test.ts:401` |
| 1 | the engine stopped: TLCGet of a key that isn't a natural number | `unit/check.test.ts:2837` |
| 1 | the engine stopped: TLCGet of a register TLC hasn't set | `unit/check.test.ts:2837` |
| 1 | the engine stopped: unsupported: TLCGet("diameter") in the search | `unit/check.test.ts:248` |
| 1 | the engine stopped: unsupported: TLCSet of a key that stops or configures TLC | `unit/tlc-pause.test.ts:8` |
| 1 | the engine stopped: values TLC can't compare: evaluating the failure again: a set TLC leaves unnormalized | `unit/native-builtins.test.ts:228` |
| 1 | the liveness checker declined: a late node TLC adds at another diameter | `unit/native-search.test.ts:1104` |
| 1 | the liveness checker declined: an atom the engine doesn't answer | `unit/native-search.test.ts:1107` |
| 1 | TLCGet, which the constant evaluator doesn't compute | `unit/check.test.ts:1034` |

### After the CLI's flip (measured 2026-11-11)

Measured at main 8165d917, after #224 flipped the CLI, with `bun scripts/run.ts check-log`:

- 1,887 checks. 1,386 print TLC's output natively and 501 are not native yet. None answered
  differently on one thread and four.
- In TLC's default mode, which writes the trace exploration spec, 245 are native. The rest wait on
  SANY's report of that spec, which the XML session owns with the other SANY reports.

What the 501 decline at, grouped by the mechanism that would make them native. "Reasons" counts the
distinct decline messages in the group.

| Mechanism | Runs | Reasons | Owner |
|---|---:|---:|---|
| Values whose text depends on how TLC built them, and sets TLC keeps lazy | 82 | 12 | S1 (lazy-values, after the memo session's guard) |
| A failure TLC words as a FingerprintException | 70 | 14 | fingerprint session |
| TLC 1.7.4 | 63 | 1 | retired: declines until the TypeScript goes |
| An assumption that fails to evaluate, evaluated again | 57 | 25 | front session |
| Temporal properties and liveness | 50 | 19 | liveness session |
| The engine stopping where TLC reports an error | 46 | 25 | memo session |
| What the constant evaluator doesn't compute | 29 | 9 | front session |
| Other failures evaluated again | 29 | 18 | memo session |
| The engine declining an operator or builtin | 19 | 15 | memo session |
| Print and PrintT where the engine can't place them | 16 | 4 | S1 (lazy-values) |
| `-dump` (`dot`, and under SYMMETRY or a VIEW) | 12 | 3 | S2 |
| Java overrides TLC loads with more than the shapes ported | 11 | 9 | unassigned |
| SANY's report of RECURSIVE declarations | 4 | 3 | XML session |
| The rest: a SYMMETRY definition's shape, a configuration error that shows a value, a configuration substitute with effects, states TLC may take for the search's under VIEW or SYMMETRY, a violating successor TLC fails to find again, and a trace the search can't step | 8 | 6 | unassigned |

The groups are checked in this order, so a decline counts once, in the first group that takes it.
The 1.7.4 runs leave with the TypeScript, and `check-log` now counts them apart, as retired with
the interpreter, without running them. The other 438 block deleting the interpreter, with native
progress events for the library's `onProgress` (see "The public API afterwards").

#### Declines to win back

Checks the binary answered and now declines, because the answer matched TLC only by chance.

- **Strings made during the search** (the string-order change; check-log on the same log, 1386
  native on main, 1384 after): `unit/check.test.ts:704` and `unit/parallel.test.ts:18` with
  `-workers 2`, both `fixtures/strings/RuntimeStrings`, where `CHOOSE` picks among
  `"q" \o ToString(n)` strings the search makes. TLC orders two strings by when it interned them,
  and it interns a string the search makes as it makes it. The store ordered two that no rank covers
  by their text, which matched TLC's creation order there by chance. It now stops on them (`an order
  of strings the search made`), and the library's tests assert TLC's output through the interpreter.
  Winning them back takes the engine ranking what it makes in TLC's order of evaluation: one worker,
  every successor and every expression in TLC's order, which a later change would have to show.

### After the FingerprintException burn-down (measured 2026-11-11)

Measured at #272 (main 924d7cd merged) with `bun scripts/run.ts check-log`:

- 1,895 checks. 1,495 print TLC's output natively and 400 are not native yet, for 147 reasons,
  listed in full under "Every reason" above. None answered differently on one thread and four.
- The declines TLC words as a FingerprintException went from 69 runs to 3: "values TLC can't
  compare" (2) and "equality of values TLC can't compare" (1).
- In TLC's default mode, which writes the trace exploration spec, 1,044 are native.

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
  WebAssembly's stack, see the measurement below.
- **S3. Tests on TLC's recordings,** recorded once with a recorder script.
- **S4. Flip and delete.**
  - `check` loses the interpreter tier, `PROVE_IT_ENGINE=0` and `PROVE_IT_LIVE_CHECK`.
  - About 24,000 lines go: `evaluate`, `values`, `environment`, `successors`, `search`, the
    interpreter's part of `check`, `liveness*`, `tableau`, `state-graph`, `builtins`, `bags`,
    `java-overrides`, `parallel*`, `worker`, `fingerprints`, `symmetry`, `randomization`,
    `transfer`, `dependencies`, `codegen`, `runtime`, `instances`, `subexpressions`,
    `spec-description`, the rest of `tlc/`, and `engine/store`, `convert`, `fingerprint`,
    `native-store` and `ir`.

### WebAssembly's stack (measured 2026-11-10)

WebAssembly's frames are on the host's stack, so a deep recursion there traps where the addon's
search thread doesn't.

- **The corpus.** The 733 Conformance models were run with the engine as WebAssembly, three
  ways: under Node with Parity's `--stack-size=8000`, under Node's default stack, and under Bun.
  No model trapped in any of the three, and each tier matched the addon's run model by model.
- **The depth.** `F(n) == IF n = 0 THEN 0 ELSE 1 + F(n - 1)` holds to about 15,000 calls under
  Node with `--stack-size=8000`, 1,800 under Node's default stack, and 1,500 under Bun, which has
  no flag to raise it. The addon recurses to the engine's bound of 20,000. TLC's JVM overflows
  at a few hundred.
- **The choice.** The engine as WebAssembly stops at 1,000 calls (`MAXIMUM_RECURSION`) and
  declines the model, so that a recursion never traps there. A trap that a deeper frame still
  causes declines too (`checkSources` in `wasm.ts`). A larger stack in a Worker, which Node alone
  offers, is optional, and an explicit stack in the evaluator isn't worth its size.

### The CLI flipped

The CLI runs each TLC command line through `checkSources` first (`checkNatively` in
`src/cli/tlc.ts`) and prints what the binary prints. Where the binary declines the model, where no
engine loads, or with `PROVE_IT_ENGINE=0`, it checks the spec as before.

What the check prints is held until the check ends. It can decline part way through the search:
- a print the relay can't word;
- a periodic configuration at its first check;
- a trace or failure the trace evaluator can't rebuild;
- the temporal properties at the end.

A model the CLI then checks the old way prints only once. Streaming waits until those declines
are few.

TLC writes a trace exploration spec unless `-noGenerateSpecTE` says not to, and the binary
doesn't yet write SANY's report of the spec TLC parses with it. So without that option, most runs
still go the old way. The corpus and the differential pass it.

What the CLI's runs declined at the flip (`bun test tests/unit` and the 733 corpus models, each
run with and without `-noGenerateSpecTE`):

| Kind | CLI test runs | Owner |
|---|---:|---|
| `java -cp …jar tlc2.TLC`: reading the version of a tla2tools.jar | 117 | the CLI (prove-it-check) |
| SANY's report of the trace exploration spec | 64 test runs, 664 corpus runs | the front end |
| TLC 1.7.4's output | 5 | retired: it declines until the TypeScript goes |
| `-dump`, `-continue` | 7 | S2 |
| the 518 of the library's `check` calls, by mechanism (above) | the rest | as staffed |

Since then, the binary reads the version of the jar on the class path from its manifest, with a
zip reader and inflater of its own (`zip.rs`, `inflate.rs`), and checks a master TLC's launch. It
declines TLC 1.7.4's jar and a manifest it can't read with certainty. Of the 117 CLI test runs, 56
now run natively; the rest decline at `-dump`, TLC 1.7.4 and the trace evaluator.

Since #250 the binary prints SANY's report of the trace exploration spec too, and checks TLC's
default natively until TLC would write the trace's files: after any error it printed a behavior for,
a counterexample or not, it declines with "the trace exploration spec TLC writes for a
counterexample". On the 733 corpus models in TLC's default, against TLC's recordings of that mode,
529 print TLC's output, 202 decline so, and 2 differ as they do with `-noGenerateSpecTE`, by TLC's
runtime (a Java stack overflow, and where TLC is installed).

### The public API afterwards

`check` and its option, progress, result and status types, `prove` and its types, `parseConfig`,
and the errors stay. `parseModule` and `Module` are the front end's to decide.

`Value`, `formatValue` and the values in `TraceStep` and `Violation` are the interpreter's classes.
The owner decided to break them: a trace step carries each variable as TLC prints it, from the
native printer, and as plain decoded data with no classes. `Value` and `formatValue` go. That is its
own change, after this one.

### What changes for users

- `PROVE_IT_ENGINE=0` goes. Where no engine loads, `EngineUnavailableError` has no escape hatch:
  - WebAssembly fails to compile;
  - or `dist` lacks the engine.
  A browser keeps the WebAssembly engine.
- A WebAssembly stack overflow becomes an error unless S2 lifts it first.
- `-dump`, `-continue` and periodic configs are checked natively. TLC 1.7.4's output is retired.
- The library prints what the binary prints. Today they differ only where the library hands over.
