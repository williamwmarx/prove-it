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

Measured at main d89e559, as the to-do list for S2 and S3. A scratch hook in `checkParsed` (not
committed) wrote each `check` call of `bun test` with a configuration given as text: its root module,
the modules it loaded, its configuration, seed, `-lncheck`, `-tool`, `-dump`, `-continue`, version and
the test that made it. 1,785 distinct calls ran through the binary with the same command line, on
one thread and with every level shared between four. Both gave the same answer for every call.

- 1,267 print TLC's output natively. Their exit codes are 0 (583), 150 (168), 12 (111), 75 (99),
  10 (97), 13 (83), 151 (54), 255 (30), 11 (17), 76 (11), 14 (8) and 77 (6).
- 518 are `not native yet`, for 195 reasons, grouped below and listed in full after.
- Besides those, the binary declines at the command line, whatever the spec: TLC 1.7.4's output
  (62 calls: `check` 50, `tlc-replay` 5, `modules` 2, `liveness` 2, `randomization`, `parallel`,
  `state-graph`; 28 of them are among the 518) and `-dump` (70 calls: `native-sets` 29,
  `native-search` 19, `native-builtins` 15, `state-graph` 7).
- Two calls have a periodic configuration (`check`). The binary prints both natively.
- No `-continue` call reached `check` through the hook.
- The hook saw no call whose configuration is an object, nor the CLI's own runs of `dist/cli.js`.

| Kind | Runs | Reasons | Test files (runs) |
|---|---:|---:|---|
| Rebuilding a run-time failure | 166 | 61 | `check` 63, `engine` 49, `native-builtins` 29, `native-search` 8, `tlc-replay` 4, `operator-constants` 4 … |
| Rebuilding a failing assumption | 97 | 39 | `check` 71, `bags` 18, `modules` 2, `json` 2, `tlc-action` 1, `exit-codes` 1 … |
| The engine stops the search | 95 | 34 | `check` 39, `native-builtins` 17, `engine` 8, `exit-codes` 6, `native-search` 5, `tlc-replay` 5 … |
| The engine declines the model | 51 | 21 | `check` 15, `native-search` 10, `native-sets` 7, `tlc-ext-operators` 6, `engine-print` 4, `operator-constants` 3 … |
| Temporal properties | 46 | 20 | `check` 15, `native-search` 8, `tlc-replay` 7, `tlc-live-level` 4, `engine` 3, `temporal` 3 … |
| Front end, configuration and printing | 33 | 13 | `check` 13, `engine-print` 5, `alias` 4, `possible` 3, `native-search` 3, `printing` 3 … |
| Constant evaluation | 30 | 7 | `check` 12, `engine` 5, `native-search` 3, `exit-codes` 2, `liveness` 2, `bags` 2 … |

#### Liveness

307 of the calls have temporal properties: 216 are native and 91 are not. 53 of those 91 are the
liveness part of this plan:
- an atom of the temporal properties that may fail to evaluate (15), and a failure in a model with
  temporal properties (5);
- the search's stops in a model with temporal properties: deadlock (5), an invariant (2), a
  division by zero (2);
- a property TLC finds a tautology, or a constant part of a temporal formula that isn't a boolean (7);
- printing where the native checker doesn't check the temporal properties (6);
- a lasso the engine doesn't hand over (5): the 2 of specs whose actions print are now native, and
  the 3 that end in the first state of their cycle (below) decline as "a step back into the cycle
  the rebuilt lasso lacks";
- an atom the engine doesn't answer (2);
- a late node at another diameter, a step back into the cycle of a spec that prints, several states
  under VIEW or SYMMETRY, and a lasso TLC fails to rebuild under a VIEW (1 each).

The other 38 are the action property violated (6, `-continue`'s native report), constant evaluation,
a constraint or VIEW that fails on a successor, and the evaluator's other gaps. The corpus has no
temporal decline: `differential --native-only` matches 1,460 of 1,466 runs, and the 6 known
differences aren't about liveness.

A lasso that ends in the first state of its cycle (the `temporal` test's three runs) is more than a
printing gap. Printing it as TLC does, stuttering at the cycle's first state, matches TLC built at
d8fb231 on those three runs. But on the binary's own `lasso-end` case the lasso differs from TLC's,
so the decline stays until the lasso's construction is traced against `LiveWorker.printTrace`.

Nothing reaches these liveness declines, so they stay declines until a test or a model does: an
accepting node under SYMMETRY or a VIEW, an unexpanded graph, uncounted branches, and every decline
of atoms that read or set TLC's registers.

#### Every reason

| Runs | Reason | Tests |
|---:|---|---|
| 16 | the engine stopped: a constraint, a VIEW or an action property that fails on a successor (with 1.7.4) | `exit-codes:99` ×3, `check:2046` ×2, `check:2002`, `check:2013`, `check:2026`, `check:2989`, `check:2994`, `check:2035`, `tlc-replay:112`, `check:2081`, `possible:110`, `check:2078`, `tlc-replay:104` |
| 14 | a constant invariant the engine checks, which TLC may warn about | `engine:708` ×2, `bags:43` ×2, `engine:809` ×2, `engine-print:183`, `engine:869`, `exit-codes:73`, `instances:43`, `native-search:1931`, `native-search:1519`, `native-search:1513`, `tlc-replay:213` |
| 12 | the engine stopped: a mistyped membership in a set of functions: evaluating the failure again: a failure TLC reports as a FingerprintException | `engine:780` ×12 |
| 11 | the engine declined: unsupported: Print | `native-search:1306` ×7, `engine-print:222` ×4 |
| 11 | the engine stopped: values TLC can't compare: evaluating the failure again: a failure TLC reports as a FingerprintException | `engine:780` ×5, `engine:743` ×3, `check:1675` ×2, `check:1576` |
| 10 | the engine stopped: a mistyped membership in a set of records: evaluating the failure again: a failure TLC reports as a FingerprintException | `engine:780` ×10 |
| 10 | the engine stopped: division by zero: evaluating the failure again: a failure TLC reports as a FingerprintException (with 1.7.4) | `check:1699` ×4, `check:1980` ×2, `check:1809`, `check:1797`, `check:1991`, `native-search:505` |
| 9 | an assumption that fails to evaluate: evaluating the assumption again: expected an integer, not a string | `check:2330` ×4, `check:3156` ×4, `check:2593` |
| 9 | printing a value whose text depends on how TLC built it | `engine-print:284` ×5, `printing:157` ×3, `native-search:1229` |
| 9 | the engine declined: unsupported: enumerating a set TLC keeps lazy (UNION at line 3) | `native-sets:248` ×4, `check:5217` ×2, `check:5206` ×2, `native-sets:311` |
| 9 | the engine stopped: a conjunct that isn't a boolean: evaluating the failure again: expected a boolean, not a integer | `check:2368` ×6, `check:2971`, `check:382`, `check:2967` |
| 8 | an assumption that fails to evaluate: evaluating the assumption again: integer overflow | `check:2330` ×6, `check:2612` ×2 |
| 7 | an assumption that fails to evaluate: evaluating the assumption again: expected a boolean, not a integer | `check:3222` ×4, `check:2330` ×2, `check:2675` |
| 7 | the engine declined: unsupported: enumerating a set TLC keeps lazy (UNION at line 5) (with 1.7.4) | `check:5116` ×4, `check:5145`, `native-sets:322`, `check:1606` |
| 7 | the engine stopped: a membership in SUBSET of a non-set: evaluating the failure again: a failure TLC reports as a FingerprintException | `engine:780` ×7 |
| 6 | the engine stopped: ToString of a value whose text depends on how TLC built it | `native-builtins:244` ×6 |
| 6 | the engine stopped: a mistyped membership in Seq: evaluating the failure again: a failure TLC reports as a FingerprintException | `engine:780` ×6 |
| 6 | the engine stopped: a mistyped membership in a set of tuples: evaluating the failure again: a failure TLC reports as a FingerprintException | `engine:780` ×6 |
| 6 | the engine stopped: a power set too large to build | `engine:1220` ×3, `engine:1346`, `engine-print:344`, `engine:696` |
| 6 | the engine stopped: an action property violated | `check:5172`, `check:5309`, `native-search:1146`, `parallel:92`, `check:579`, `check:974` |
| 6 | the engine stopped: an atom of the temporal properties that may fail to evaluate (with 1.7.4) | `tlc-live-level:18` ×2, `tlc-replay:225` ×2, `engine:1240`, `tlc-live-level:25` |
| 5 | a POSTCONDITION or an ALIAS TLC may compute as it starts | `alias:70` ×2, `possible:118`, `possible:123`, `alias:89` |
| 5 | a division by zero, which the constant evaluator doesn't compute (with 1.7.4) | `liveness:111` ×2, `check:1300`, `check:5562`, `check:5507` |
| 5 | a property TLC finds a tautology (with 1.7.4) | `check:5524` ×2, `check:5316` ×2, `check:5194` |
| 5 | a temporal property's counterexample: a lasso the engine doesn't hand over | `temporal:96` ×3, `engine-print:272`, `native-search:1027` |
| 5 | an assumption that fails to evaluate: evaluating the assumption again: SUBSET of a non-set | `check:2330` ×4, `check:2583` |
| 5 | an assumption that fails to evaluate: evaluating the assumption again: it didn't fail | `check:3125`, `check:194`, `check:2776`, `bags:97`, `check:2330` |
| 5 | an assumption that fails to evaluate: evaluating the assumption again: the builtin BagOfAll | `bags:128` ×3, `bags:97`, `bags:120` |
| 5 | the engine stopped: an atom of the temporal properties that may fail to evaluate: evaluating the failure again: expected a boolean, not a integer | `check:2428` ×2, `check:2443` ×2, `tlc-replay:150` |
| 5 | the engine stopped: an operator's table applied outside its rows: evaluating the failure again: an operator's table applied outside its rows | `operator-constants:81` ×3, `native-search:1801`, `operator-constants:49` |
| 5 | the engine stopped: deadlock (with 1.7.4) | `check:2521` ×2, `tlc-replay:185` ×2, `tlc-replay:167` |
| 5 | the engine stopped: enumerated Nat | `check:1934` ×2, `check:3101` ×2, `check:1951` |
| 5 | the engine stopped: unsupported: TLCGet of a key the search doesn't keep (with 1.7.4) | `check:2837`, `check:248`, `tlc-statistics:25`, `check:5379`, `check:5378` |
| 4 | a _POSSIBLE predicate the search didn't witness | `native-search:1547`, `check:282`, `native-search:1543`, `possible:66` |
| 4 | an assumption that fails to evaluate: evaluating the assumption again: expected a sequence, not 1 (with 1.7.4) | `check:2330` ×2, `check:2339` ×2 |
| 4 | an assumption that fails to evaluate: evaluating the assumption again: expected an integer, not a set | `check:2330` ×4 |
| 4 | rebuilding a trace: the builtin Trace | `tlc-ext:23`, `alias:48`, `alias:59`, `alias:28` |
| 4 | the engine stopped: SubSeq outside the sequence's domain: evaluating the failure again: SubSeq outside the sequence's domain | `native-builtins:228` ×4 |
| 4 | the engine stopped: applied a function outside its domain: evaluating the failure again: a failure TLC reports as a FingerprintException (with 1.7.4) | `check:5259`, `check:1627`, `check:5266`, `tlc-replay:95` |
| 4 | the engine stopped: applied a function outside its domain: evaluating the failure again: applied a function outside its domain | `check:1896`, `check:1830`, `check:1874`, `native-search:505` |
| 4 | the engine stopped: applied a function outside its domain: evaluating the failure again: values TLC can't compare (with 1.7.4) | `check:2573` ×4 |
| 4 | the engine stopped: expected a boolean: evaluating the failure again: expected a boolean, not a function | `check:1403` ×4 |
| 4 | the engine stopped: recursion too deep | `check:2928`, `exit-codes:75`, `exit-codes:71`, `exit-codes:72` |
| 4 | the engine stopped: unsupported: comparing a function TLC keeps lazy | `native-search:505` ×3, `native-builtins:228` |
| 4 | values TLC can't compare, which the constant evaluator doesn't compute | `check:1257` ×3, `exit-codes:84` |
| 3 | a SYMMETRY definition that isn't an operator applied to its sets | `check:1243` ×2, `exit-codes:57` |
| 3 | a constant definition the configuration names | `check:5014`, `check:5019`, `check:5011` |
| 3 | a value that isn't a set where TLC wants one, which the constant evaluator doesn't compute (with 1.7.4) | `check:5562` ×3 |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: a membership in a set, which isn't a set | `check:2760`, `check:2754`, `check:2717` |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: enumerated an infinite set | `bags:97` ×2, `check:2675` |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: expected an integer, not a function | `check:2330` ×3 |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: the builtin AssertEq | `check:770` ×2, `json:28` |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: the builtin SubBag | `bags:120`, `check:501`, `bags:97` |
| 3 | an assumption that fails to evaluate: evaluating the assumption again: values TLC can't compare | `check:3248` ×3 |
| 3 | temporal quantification in the specification | `specifications:68` ×2, `exit-codes:109` |
| 3 | the engine declined: unsupported: PickSuccessor | `tlc-ext-operators:48`, `tlc-ext-operators:54`, `tlc-ext-operators:61` |
| 3 | the engine stopped: EXCEPT outside the domain (with 1.7.4) | `check:2573` ×2, `check:1627` |
| 3 | the engine stopped: a guard that isn't a boolean: evaluating the failure again: expected a boolean, not a integer | `tlc-replay:62`, `check:2975`, `exit-codes:52` |
| 3 | the engine stopped: a predicate that isn't a boolean: evaluating the failure again: expected a boolean, not a integer | `check:2075`, `check:2072`, `check:2002` |
| 3 | the engine stopped: an invariant violated (with 1.7.4) | `check:2521` ×2, `check:644` |
| 3 | the engine stopped: an order of strings the search ranked | `native-builtins:279` ×2, `native-builtins:327` |
| 3 | the engine stopped: enumerated a set TLC can't enumerate: evaluating the failure again: enumerated an infinite set | `check:3043`, `check:2407`, `check:1914` |
| 3 | the engine stopped: expected a set: evaluating the failure again: expected a set, not a integer | `native-builtins:228` ×3 |
| 3 | the engine stopped: expected an integer: evaluating the failure again: expected an integer, not a string | `tlc-replay:57`, `tlc-replay:51`, `exit-codes:52` |
| 3 | the engine stopped: no CASE arm holds: evaluating the failure again: no CASE arm holds | `check:2407`, `check:3055`, `check:1521` |
| 3 | the engine stopped: record compared with a function | `engine:618` ×2, `engine:743` |
| 3 | the engine stopped: variable not assigned: evaluating the failure again: it didn't fail | `native-search:1161`, `check:1859`, `check:1854` |
| 2 | SANY's report of a module-level RECURSIVE declaration that something else binds, or an INSTANCE may: F | `check:3442`, `check:4626` |
| 2 | a constant part of a temporal formula that isn't a boolean | `check:5337` ×2 |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: SubSeq outside the sequence's domain | `check:2330` ×2 |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: TLCGet | `tlc-action:10`, `tlc-revision:26` |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: a bag that isn't a function | `bags:97` ×2 |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: applied a function outside its domain | `check:2692`, `check:2695` |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: expected a set, not a integer | `check:2675` ×2 |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: the builtin ToJson@Json (with 1.7.4) | `modules:152` ×2 |
| 2 | an assumption that fails to evaluate: evaluating the assumption again: the builtin \sqsubseteq | `bags:120`, `bags:97` |
| 2 | an operator, which the constant evaluator doesn't compute | `check:5337`, `engine-ir:198` |
| 2 | the engine declined: the builtin EmptyBag@Bags, whose value the interpreter computes | `modules:136` ×2 |
| 2 | the engine declined: unsupported: F | `operator-constants:33` ×2 |
| 2 | the engine declined: unsupported: PrintT | `tlc-constraint-order:11`, `tlc-statistics:11` |
| 2 | the engine declined: unsupported: enumerating a set TLC keeps lazy (Product at line 5) (with 1.7.4) | `check:5116` ×2 |
| 2 | the engine stopped: CHOOSE found no element: a failure in a model with temporal properties (with 1.7.4) | `tlc-replay:138` ×2 |
| 2 | the engine stopped: Print inside ENABLED | `engine-print:251`, `native-search:1314` |
| 2 | the engine stopped: TLCExt's Trace, the behavior the engine doesn't keep | `tlc-ext:17`, `tlc-ext:30` |
| 2 | the engine stopped: ToString of a text the engine made unranked | `native-builtins:279`, `native-builtins:491` |
| 2 | the engine stopped: a CASE condition that isn't a boolean: evaluating the failure again: expected a boolean, not a integer | `check:2407` ×2 |
| 2 | the engine stopped: a tuple pattern that doesn't match: evaluating the failure again: a tuple pattern that doesn't match | `native-search:1388`, `native-search:1360` |
| 2 | the engine stopped: an IF condition that isn't a boolean: evaluating the failure again: expected a boolean, not a integer | `check:2407` ×2 |
| 2 | the engine stopped: an atom of the temporal properties that may fail to evaluate: evaluating the failure again: enumerated an infinite set | `engine:1088`, `check:2428` |
| 2 | the engine stopped: division by zero (with 1.7.4) | `check:2508` ×2 |
| 2 | the engine stopped: division by zero: a failure in a model with temporal properties (with 1.7.4) | `tlc-replay:138` ×2 |
| 2 | the engine stopped: equality of values TLC can't compare: evaluating the failure again: equality of values TLC can't compare | `check:1416` ×2 |
| 2 | the engine stopped: expected a function: evaluating the failure again: a bag that isn't a function | `native-builtins:228` ×2 |
| 2 | the engine stopped: printing where the native checker doesn't check the temporal properties: a predicate the engine leaves to the interpreter (with 1.7.4) | `check:2466` ×2 |
| 2 | the engine stopped: printing where the native checker doesn't check the temporal properties: prints it doesn't place in TLC's order | `native-search:1074`, `native-search:1058` |
| 2 | the engine stopped: unsupported: a state holding a function TLC keeps lazy | `check:1963`, `check:1934` |
| 2 | the engine stopped: values TLC can't compare: evaluating the failure again: a set TLC leaves unnormalized | `check:1675`, `native-builtins:228` |
| 2 | the liveness checker declined: an atom the engine doesn't answer | `tlc-live-level:18`, `native-search:1106` |
| 1 | SANY's report of a RECURSIVE declaration of a name a module binds or names before it: F | `check:4677` |
| 1 | SANY's report of a module nested in another that declares RECURSIVE R | `check:4626` |
| 1 | TLCGet, which the constant evaluator doesn't compute | `check:1034` |
| 1 | a CHOOSE no element of which satisfies, which the constant evaluator doesn't compute | `check:1290` |
| 1 | a configuration error that shows a value | `check:5027` |
| 1 | a configuration substitute with effects, which TLC evaluates at every use: C <- Foo | `check:1040` |
| 1 | a temporal property's counterexample: a step back into the cycle of a spec that prints | `counter-example:38` |
| 1 | a violating successor TLC fails to find again from its generator | `randomization:41` |
| 1 | an ALIAS without a definition | `alias:70` |
| 1 | an assumption that fails to evaluate: an assumption the engine found to hold that doesn't again | `check:69` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: Head of the empty sequence | `check:2330` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: JsonDeserialize, whose file the replay doesn't read or write | `json:34` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: Tail of the empty sequence | `check:2330` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: a SelectSeq test that isn't a boolean | `check:2330` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: a bag whose count isn't an integer | `bags:120` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: a bag with a count that isn't positive | `bags:97` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: a power set too large to build | `check:3084` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: evaluating a an unbounded quantifier | `check:1473` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: expected a boolean, not a set | `check:3222` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: expected a sequence, not "ab" | `check:2330` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: expected an integer, not a boolean | `check:2330` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: no CASE arm holds | `check:1453` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: recursion too deep | `exit-codes:77` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: the builtin BagIn | `bags:97` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: the builtin IsABag | `bags:120` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: the builtin ToJson | `check:761` |
| 1 | an assumption that fails to evaluate: evaluating the assumption again: the builtin Trace | `tlc-ext-operators:40` |
| 1 | no step from state N is the trace's next | `check:721` |
| 1 | several states TLC may take for the search's under VIEW or SYMMETRY | `native-search:870` |
| 1 | the engine declined: checking an assumption again: an assumption the engine doesn't evaluate that fails to: AssertError of a message that isn't a string | `tlc-ext-operators:69` |
| 1 | the engine declined: unsupported: AssertEq | `tlc-ext-operators:27` |
| 1 | the engine declined: unsupported: Inc | `operator-constants:45` |
| 1 | the engine declined: unsupported: Print where TLC evaluates it otherwise | `native-search:1306` |
| 1 | the engine declined: unsupported: RandomElement | `randomization:142` |
| 1 | the engine declined: unsupported: TLCGetAndSet | `tlc-ext-operators:94` |
| 1 | the engine declined: unsupported: UNCHANGED in the initial predicate | `native-search:1396` |
| 1 | the engine declined: unsupported: a value TLC computed at startup with effects | `native-search:1641` |
| 1 | the engine declined: unsupported: enumerating a lazy set of the state under a VIEW | `check:2155` |
| 1 | the engine declined: unsupported: enumerating a set TLC keeps lazy (Alias: UNION at line 5) | `native-sets:333` |
| 1 | the engine declined: unsupported: enumerating a set TLC keeps lazy (UNION at line 4) | `check:5206` |
| 1 | the engine declined: unsupported: expression UnboundedQuantifier | `bundled-modules:16` |
| 1 | the engine declined: unsupported: walking a lazy function over a tuple | `check:1830` |
| 1 | the engine stopped: BagCardinality of a non-bag: evaluating the failure again: a bag whose count isn't an integer | `native-builtins:228` |
| 1 | the engine stopped: BagCardinality of a non-bag: evaluating the failure again: a bag with a count that isn't positive | `native-builtins:228` |
| 1 | the engine stopped: BagOfAll of a literal | `native-builtins:228` |
| 1 | the engine stopped: EXCEPT on a non-function: evaluating the failure again: Attempted to apply EXCEPT construct to the value 1. | `check:2573` |
| 1 | the engine stopped: EXCEPT on a non-function: evaluating the failure again: a failure TLC reports as a FingerprintException | `check:1627` |
| 1 | the engine stopped: RandomSubset of a product too large to index | `native-builtins:390` |
| 1 | the engine stopped: RandomSubset of an interval too large to draw from | `native-builtins:401` |
| 1 | the engine stopped: SortSeq of a non-sequence: evaluating the failure again: the builtin SortSeq | `native-builtins:228` |
| 1 | the engine stopped: SubBag of a non-bag: evaluating the failure again: the builtin SubBag | `native-builtins:228` |
| 1 | the engine stopped: SubSeq of a non-sequence: evaluating the failure again: expected a sequence, not {1} | `native-builtins:228` |
| 1 | the engine stopped: TLCGet of a key that isn't a natural number | `check:2837` |
| 1 | the engine stopped: TLCGet of a register TLC hasn't set | `check:2837` |
| 1 | the engine stopped: TLCModelValue of a value that isn't a string: evaluating the failure again: TLCModelValue of a value that isn't a string | `native-builtins:334` |
| 1 | the engine stopped: a SelectSeq test that isn't a boolean: evaluating the failure again: a SelectSeq test that isn't a boolean | `native-builtins:228` |
| 1 | the engine stopped: a VIEW that fails on an initial state | `engine-symmetry:93` |
| 1 | the engine stopped: a guard that isn't a boolean: evaluating the failure again: a failure TLC reports as a FingerprintException | `check:1854` |
| 1 | the engine stopped: action composition: evaluating the failure again: a next-state relation the IR holds no actions of (with 1.7.4) | `check:5407` |
| 1 | the engine stopped: an atom of the temporal properties that may fail to evaluate: evaluating the failure again: an EvalException adding an initial state | `exit-codes:104` |
| 1 | the engine stopped: an atom of the temporal properties that may fail to evaluate: evaluating the failure again: it didn't fail | `engine:1123` |
| 1 | the engine stopped: an initial state that isn't complete: evaluating the failure again: an initial state that isn't complete | `exit-codes:52` |
| 1 | the engine stopped: an invariant violated: a _POSSIBLE predicate | `possible:72` |
| 1 | the engine stopped: an order of model values the search ranked | `native-builtins:315` |
| 1 | the engine stopped: an overflow counting the elements of a power set: evaluating the failure again: a state TLC fingerprints only where its constraints hold | `check:2121` |
| 1 | the engine stopped: an overflow counting the elements of a power set: evaluating the failure again: an action that fails or prints after a successor TLC can't fingerprint | `check:2137` |
| 1 | the engine stopped: applied a function outside its domain: rebuilding a trace: primed variable not assigned: x | `native-search:1460` |
| 1 | the engine stopped: applied a non-function: evaluating the failure again: a failure TLC reports as a FingerprintException | `check:1627` |
| 1 | the engine stopped: division by zero: a failure with a POSTCONDITION | `possible:110` |
| 1 | the engine stopped: drew from a set whose shape the engine forgets | `native-builtins:417` |
| 1 | the engine stopped: enumerated [D -> R] with R infinite | `native-sets:169` |
| 1 | the engine stopped: enumerated a filter of an infinite set: evaluating the failure again: a state whose fingerprint the replay doesn't follow | `check:1944` |
| 1 | the engine stopped: enumerated a non-set: a failure in a model with temporal properties | `check:2489` |
| 1 | the engine stopped: enumerated a product of an infinite set | `native-sets:169` |
| 1 | the engine stopped: enumerated a set TLC can't enumerate: evaluating the failure again: a failure TLC reports as a FingerprintException | `native-sets:207` |
| 1 | the engine stopped: enumerated an infinite set | `native-sets:169` |
| 1 | the engine stopped: enumerated an operation on infinite sets | `bundled-modules:23` |
| 1 | the engine stopped: equality of values TLC can't compare: evaluating the failure again: a failure TLC reports as a FingerprintException | `check:1416` |
| 1 | the engine stopped: equality of values TLC can't compare: evaluating the failure again: the builtin BagIn | `native-builtins:228` |
| 1 | the engine stopped: expected a bag: evaluating the failure again: it didn't fail | `native-builtins:228` |
| 1 | the engine stopped: expected a boolean: evaluating the failure again: a failure TLC reports as a FingerprintException | `native-sets:169` |
| 1 | the engine stopped: expected a function: evaluating the failure again: the builtin BagIn | `native-builtins:228` |
| 1 | the engine stopped: expected a function: evaluating the failure again: the builtin BagOfAll | `native-builtins:228` |
| 1 | the engine stopped: expected a function: evaluating the failure again: the builtin SubBag | `native-builtins:228` |
| 1 | the engine stopped: expected a function: evaluating the failure again: the builtin \sqsubseteq | `native-builtins:228` |
| 1 | the engine stopped: expected a sequence: evaluating the failure again: expected a sequence, not "ab" | `native-builtins:228` |
| 1 | the engine stopped: expected a set: evaluating the failure again: expected a set, not a function | `native-builtins:228` |
| 1 | the engine stopped: expected an integer: evaluating the failure again: a bag whose count isn't an integer | `native-builtins:228` |
| 1 | the engine stopped: expected an integer: evaluating the failure again: the builtin CopiesIn | `native-builtins:228` |
| 1 | the engine stopped: expected an integer: evaluating the failure again: the builtin SortSeq | `native-builtins:228` |
| 1 | the engine stopped: expected an integer: evaluating the failure again: the builtin SubBag | `native-builtins:228` |
| 1 | the engine stopped: printing where the native checker doesn't check the temporal properties: a node that accepts every behavior | `native-search:1046` |
| 1 | the engine stopped: printing where the native checker doesn't check the temporal properties: steps from states it didn't store | `native-search:826` |
| 1 | the engine stopped: quantified over a non-set: evaluating the failure again: expected a set, not a integer | `native-search:505` |
| 1 | the engine stopped: unsupported: TLCGet("diameter") in the search | `check:248` |
| 1 | the engine stopped: unsupported: TLCSet of a key that stops or configures TLC | `tlc-pause:8` |
| 1 | the liveness checker declined: a late node TLC adds at another diameter | `native-search:1103` |

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
