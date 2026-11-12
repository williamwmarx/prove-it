# No TypeScript engine fallback

**Superseded (PR 7, 2026-11-12).** The interpreter, the TypeScript checker and TLC 1.7.4's output
are deleted. The library's `check` and the CLI run the native check alone: where it declines a
model, `check` throws `TlaUnsupportedError` with `not native yet: <reason>`, and the CLI prints
`prove-it: not native yet: <reason>` and exits 1. `PROVE_IT_ENGINE=0` is gone. The rest of this
file records the plan as it stood before.

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
the search. The TypeScript report is deleted: what it printed, tla-front prints or declines, and
its tests are tla-front's `tests/report-cases`, each recorded from TLC at d8fb231 or TLC 1.7.4.
TLC 1.7.4's warnings alone match (case 22), and its semantic errors decline (cases 19, 20, 34
and 35), which the TypeScript report printed: whether to port 1.7.4's generator differences or
retire them with 1.7.4 is open.

SANY's messages come from the port of its generator and levelCheck, which declines a message whose
shape no recording shows, and else from linking. Linking takes the standard modules as TLC ships
them, which a spec that replaces one another standard module reads, such as its own Naturals
under Sequences, may not keep: main's binary printed no errors for a Naturals without `..`, where SANY
reports 24 (tests/report-cases/38), which the generator now writes. Where the generator declines
such a spec, linking declines too ("SANY's messages of the standard modules with one of them
replaced").

Seven adversarial runs against TLC at d8fb231 (about 1,440 runs of 620 specs, 680 more specs,
2,149 runs of handwritten and corpus-mutated specs, 1,876 more inputs, 6,571 more, 951 of a
spec's paths and files, then 4,350 more, in TLC's default mode and with `-noGenerateSpecTE`) and review found the
report wrong or declining for 2,113; each is a case of tla-front's `tests/sany-cases`, recorded in
`sany-cases.json`, whose `case.json` gives the reason where the front end declines it. All print
what TLC prints but these, which decline:
- a module SANY's parser accepts and the front end's rejects (36 cases): a definition of the
  postfix operator `'` (`a' == a`, `a ' == 1`), proofs nested more than 100 deep, where SANY's
  parser stops, and mutations whose parse the front end reads otherwise;
- a module of the CommunityModules that no file beside the spec holds, or a module of TLC's that
  extends one, such as `_DotTrace` or `_CBORTrace` (155 cases): TLC finds it where
  CommunityModules.jar is beside tla2tools.jar, and else reports it missing, which the TypeScript
  report printed;
- SANY's generator throwing on the root module after a module of the user's (2 cases; main's
  binary declined);
- a proof's INSTANCE of a module the spec doesn't otherwise depend on (72 cases), which SANY's
  ParseUnit.getInstances loads and the front end doesn't yet;
- a HIDE of an expression SANY's generator leaves null, such as `HIDE 1 + 1` without Naturals,
  for which SANY throws a NullPointerException (9 cases);
- a record field named like a definition whose value applies a recursive operator, on which
  SANY's linter overflows its stack (4 cases);
- `@` as a DEF clause entry, which SANY reports as an unknown operator (2 cases);
- a module nested at the top of a module that its extender extends, which
  ParseUnit.handleExtensions lets the extender's EXTENDS and INSTANCE name, and the front end
  looks for in a file, where the loader that binds names to inner modules of extended files
  doesn't bind them unambiguously (12 cases; it prints the other 9 of the 21 as TLC does);
- LETs nested 100 deep in their definitions, where SANY's generator throws (1 case);
- brackets nested so deep that SANY's parser may overflow Java's default stack: past 1,100,
  counting a square bracket twice, where Java overflows past about 1,500 parentheses, braces or
  angle brackets and 900 function constructors. Other forms nested as deep, such as IF or `\A`,
  are not counted, and may print where TLC overflows (1 case).

Linking declines a parameterized INSTANCE of a standard module, whose operators it gave no
parameters (`I(p) == INSTANCE Integers` with `I(1)!Int`): main's binary printed that `I!Int`
requires -1 arguments. Where the binary declines, the CLI falls back to the TypeScript engine,
which still prints that error after SANY's report, as it prints other errors its linking raises,
such as for `EXTENDS _JsonTrace`, as SANY's. How TLC finds, reads and names a spec's files, which
the last run probed, is TLC's resolver's, as main has it; what that run found there is for the
resolver, not the report.

TLC prints a character of a message outside ASCII as `?` under a locale that isn't UTF-8, where
Prove It prints the character; the runs above compare under `C.UTF-8`. The CLI's own command line,
which names several specs, a spec by its configuration file or a glob, is not TLC's.

A message of the generator whose shape no recording shows is printed where linking gives the same
messages, and where linking can't give them, as the TypeScript report, a port of the same
generator, printed them; where linking gives others, the report declines ("SANY's messages,
which linking gives apart from SANY's generator").

### Decision: the CLI finds a spec's files with the engine

Settled on 2026-11-11, as the CLI's TypeScript copy of TLC's resolver is deleted: the CLI finds the
spec, its config, its modules and its Java overrides as the binary does, through `prove-it-host`'s
`resolveFiles` and `checkSources`, which name the paths they stat, read and resolve, the working
and temporary directories and the platform, for JavaScript to answer. Paths follow the host's rules
(`prove-it-check/src/host_path.rs`, Node's `path` for the platform, as the TypeScript resolver used
it): the binary and the addon take them from the target they were built for, and the WebAssembly
engine from the platform JavaScript names, so a Windows host without the addon reads `;` lists,
drives and UNC paths. So `PROVE_IT_ENGINE=0` means, here too, that
the interpreter searches, not that no native code runs. An install without the platform package
checks with the WebAssembly engine beside `dist/cli.js` (`tests/unit/native.test.ts` runs a copy of
`dist/` that no package resolves from). The CLI throws `EngineUnavailableError` only where an engine
`PROVE_IT_ENGINE_ADDON` or `PROVE_IT_ENGINE_WASM` names, or an executable embeds, fails to load, or
where neither the addon nor the WebAssembly engine loads. Its message then names no setting, since
none checks without the engine. The library's `check` of a source string reads no file and is
unchanged.

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
  instance and returns a stop that hands nothing over (src/engine/wasm.ts). The CLI's interpreter
  then searches from the start; the library's check throws `WebAssemblyStackError` instead, as it
  does where the engine stops at its recursion bound.

### Interpreter limits

Where the native check declines, the library's `check()` passes the TypeScript check's prints of
a violation's trace to `onPrint` as TLC prints them, but for three shapes, where the TypeScript
check places them otherwise than TLC or prints other values in them: an ALIAS that prints, a
temporal property that prints, and TLCExt's `Trace`. There `onPrint` gets what the TypeScript
check printed as it searched, as where the native check doesn't run (`onProgress`, `onPause`, a
`dot` dump, TLC 1.7.4). `tests/unit/trace-prints.test.ts` pins them; they go with the interpreter.

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
- **A WebAssembly stack overflow.** The library's check throws `WebAssemblyStackError`; the CLI's
  interpreter searches from the start.
- **`PROVE_IT_LIVE_CHECK=1`.** It cross-checks the native liveness verdict.

Neither side implements `-simulate`, `-generate`, `-debug` or `-loadTrace`. The binary writes
`-dumpTrace tlc` and `-dumpTrace json`, and declines the other formats and the cases cli.md's
"-dumpTrace" lists; the interpreter writes none. It prints `-coverage`'s report and declines the
cases cli.md's "-coverage" lists: its "Not native" list, the cut, `-continue` carried past a
violation, and estimates without `-fp` that differ by polynomial.
`src/pcal` only validates for SANY, and `src/prover`, the wrapper of the Rust prover driver,
imports only `worker.ts`'s thread helpers (`isWorkerSupported`, `spawnWorker`,
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

Measured again on main f941e35 with a check that fails on a deadlocked state, what a model with
temporal properties prints at a stop, and TLC's errors for a tautology and a non-boolean constant
part, with `check-log` counting TLC 1.7.4's checks apart (63, retired with the interpreter): 287 of
the other checks have temporal properties, 245 are native and 42 are not. 12 of those 42 are the
liveness part of this plan, down from 22:
- a failure in a model with temporal properties: an atom of the temporal properties that may fail
  to evaluate, and SUBSET of a non-set evaluated again after Next fails (1 each);
- a division by zero in Next where a late node of that state runs Next again, which TLC fails on a
  second time, evaluating the checks again (1);
- printing where the native checker doesn't check the temporal properties (5): prints it doesn't
  place in TLC's order (2), a node that accepts every behavior, a predicate the engine leaves to the
  interpreter, and steps from states it didn't store (1 each);
- an atom the engine doesn't answer, a late node at another diameter, a step back into the cycle of
  a spec that prints, and several states under VIEW or SYMMETRY (1 each).

Of the other 30: constant evaluation (9), a constraint, a VIEW or an action property that fails on
a successor (8), a power set too large to build (3), `-dump` (3), PrintT where the engine can't
place it (2), and five more of the evaluator's and the front end's gaps (1 each).

A deadlock in a model with temporal properties prints TLC's output where a check fails as TLC adds
the deadlocked state to the behavior graphs: the deadlock, the trace, then that check's call stack
([liveness.md](liveness.md)). It declines a check that reads a definition an INSTANCE copies, whose
call stack in TLC holds the INSTANCE as a frame. A spec that prints, stopped by a deadlock, a violated invariant or
action property, or a failure of Next or an invariant, prints what TLC prints at the stop, in TLC's
order, the prints of adding the stopped state after the trace included (liveness.md, "Print at a
stop"). It declines a late node of a state whose next states fail, one whose full Next takes
other steps than the search took, and an invariant that prints which the configuration lists twice,
which TLC checks twice.

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
as `\b101`, or else the part's location. Where the part is an expression an INSTANCE puts in for
a declaration of the module it instantiates, TLC's `SubstInNode` keeps the declaration's node and
binds it to the expression's value (`Liveness.astToLive`), so TLC names the declaration where the
instantiated module writes it, which the front end doesn't keep: that declines wherever the part
is, or is within, a substitute or what the front end makes of one (a LET or IF it folds, an
operator it calls, a substitute a later INSTANCE or a renaming copies). TLC takes a property's
label whole, and unrolls a property's \A with the substitutions of the INSTANCEs it went through
left unbound, taking the \A whole where reading one fails (`SpecProcessor.processConfigProps`).
The front end unrolls a \A as main does, with the substitutions bound, so it declines, as main
does, a tautology or a constant part that isn't a boolean in a property where it unrolled a \A
(see "Declines to win back"). A grid of 113 small specs
(`prove-it-cli/tests/live-startup-grid`) prints what TLC prints on 608 of its 904 runs; the others
decline, for the constant evaluator's gaps, a substituted declaration, an unrolled \A, a constant
definition TLC may print as it starts before the error, or a tautology
after a state-level property, which TLC warns of first. Four name an
INSTANCE's definition before the INSTANCE, which SANY doesn't know there.

Nothing reaches these liveness declines, so they stay declines until a test or a model does:
- an accepting node under SYMMETRY or a VIEW;
- an unexpanded graph;
- uncounted branches;
- every decline of atoms that read or set TLC's registers.

One corpus model stops at an atom the engine doesn't answer: MisraReachability's MCParReach,
whose `PROPERTY Refines` is `R!Spec`, with `R == INSTANCE Reachable WITH vroot <- vrootBar, pc <-
pcBar`. The engine doesn't compile the action atom of `R!Spec`, whose `\E v \in vroot` enumerates
the substitute `vrootBar == vroot \cup UNION {toVroot[i] : i \in Procs}` read in the INSTANCE's
scope: a set TLC keeps lazy, of which the compiled substitute keeps no reference (`enumerating a
set TLC keeps lazy (vrootBar@ParReach: \cup at line 0)`). An atom the engine doesn't answer is one
TLC may fail at as it adds the initial state, so the search stops there, and replaying the atom
finds no failure: the binary and the library decline it ("the engine stopped: an atom of the
temporal properties that may fail to evaluate: evaluating the failure again: it didn't fail"),
where TLC checks it (747 states generated, 393 distinct). Written in the root module as
`R!Init /\ [][R!Next]_R!vars /\ WF_R!vars(R!Next)`, the property is native: TLC and the binary
both fail there ("In evaluation, the identifier vroot is either undefined or not an operator.").
Winning it back takes compiling a substitute's set with its lazy reference where an atom reads it
in an INSTANCE's scope.

#### Action constraints that fail to evaluate

An ACTION_CONSTRAINT that fails to evaluate on a step is native: TLC throws out of
`Worker.addElement` before it counts the successor as found and reports the error as one of the
next states (`ModelChecker.doNextFailed`), with the trace to that successor, then the call stack of
its replay of the expansion with its `CallStackTool` (`ModelChecker.doNext`), as in
`prove-it-cli/tests/action-constraint-failures` (from the grid of 796 runs: 744 match, 52
decline, none differ). What still declines:
- an action constraint that is a literal and no boolean (`AC == "yes"`): TLC fails casting the
  definition it holds for it, with a ClassCastException whose message names the JVM's classes
  (`a constraint that is a literal, which TLC fails to cast`), as for a CONSTRAINT;
- one that fails under `-continue`, or with an ALIAS, `-dumpTrace`, a property TLC checks of each
  step (`[][A]_v`), or online liveness checking;
- one after which an atom of the temporal properties fails as TLC adds the state it was
  expanding to the behavior graphs: TLC then prints the atom's call stack with the trace to the
  successor, which isn't followed;
- one whose replay doesn't follow TLC: a successor before it TLC fails to fingerprint, one
  outside the model that violates an invariant, a next-state relation the evaluator doesn't split
  into TLC's actions, or a step that no longer fails;
- one the configuration binds (`= TRUE` outside a module scope, or `<-`), whose definition the
  search evaluates where TLC holds the value and drops the constraint bound to TRUE (`a failing action constraint the
  configuration binds`);
- a CONSTRAINT or a VIEW that fails to evaluate on a successor, as before (`a constraint, a VIEW
  or an action property that fails on a successor`).

#### Declines to win back

A correctness fix can turn a run that matched TLC into a decline, where the engine can't yet tell
it from one that printed something else. Each is outside the corpus:
- a SYMMETRY definition with parameters, whose body TLC evaluates without them
  (`Tool.getSymmetryPerms`), failing at the first parameter it reads or going on with the value.
  The front end reported that it isn't a set of permutations, which TLC never prints for one; it
  declines it (`a SYMMETRY definition with parameters`).
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
- a configuration substitute `C <- D`, and an operator a TLCOverrides index replaces, where TLC
  computes the definition or the Java method again at each read: TLC holds C as D's definition, so
  it prints, draws and sets registers again wherever it reads C, and calls a `final` method without
  parameters as it loads it (`MethodValue.get`). Native runs keep main's behaviour, which matches
  only where nothing after the read shows the difference, and prints other output where something
  does. The groups: register readers, TLCGet("level") printers, invisible override reads, random
  draws, final methods, VIEW and POSTCONDITION reads, and recursive-operator arguments. The
  `front-constants-full` branch declines them where the run computes the read
  (`Definition::READ_DECLINED`) and reads the index. Its 13,067 adversarial specs, against TLC at
  d8fb231, on the `front-constants-cases` branch, are the regression set for winning them back.
  Where a substitute reaches AssertEq, TLCGetOrDefault, TLCGetAndSet or PickSuccessor, where a
  constant definition or an assumption reads TLCExt's registers, or where only those builtins make
  a constant definition impure, the IR marks the four `Builtin::DECLINED`, and the engine declines
  them where it computes them, as it did before it checked them.
- an action constraint that applies a constant function outside its domain
  (`f == [i \in 0..2 |-> i]`, `AC == f[x'] > 0`, the failDom* cases of
  `prove-it-cli/tests/action-constraint-failures`). TLC words the failure with the `FcnRcdValue` it
  computed as it started (`Attempted to apply function:`), which the evaluator doesn't build, so
  the binary declines it (`applied a function outside its domain`), as it did before action
  constraint failures were native. To win them back, build a constant definition's function as
  TLC computed it at startup.
- SANY's report of a spec that extends a module of the CommunityModules (`EXTENDS SequencesExt`)
  that no file beside the spec holds. The TypeScript report printed that SANY can't find it,
  which TLC prints only where CommunityModules.jar isn't beside tla2tools.jar: it matched TLC by
  where the jar was. The report declines it, as the binary did; winning it back takes knowing
  whether TLC's class path holds the CommunityModules.

A property's \A that TLC unrolls, or takes whole, with the substitutions of the INSTANCEs it went
through left unbound declines where it is a tautology or has a constant part that isn't a boolean,
as on main. Branch `live-stops-full` follows TLC's lookup there: lazy operator arguments, LET
definitions and closures read in the context they are written in, a definition named from outside
its INSTANCE entered through its own `SubstInNode`, and root constants and configuration overrides
read past an INSTANCE. Eight adversarial rounds kept finding edges in it (nested INSTANCEs that
substitute a bare name, operator arguments naming an INSTANCE's copy), so it waits there.

#### Known wrong outputs

The engine and the trace evaluator test a union, an equality of sets and a membership in a UNION
in an order other than the one in which TLC holds the sets' elements unnormalized, so a failure
there names other elements than TLC's, and AssertError, which compares that message, answers FALSE
where TLC answers TRUE (found by #327's adversarial round; each wrong on main alike):

| Repro | TLC | Native |
|---|---|---|
| `AssertError("Attempted to check equality of integer 2 with non-integer:\n\"a\"", 1 \in {2, 1} \cup {"a"})` | TRUE | FALSE (the bare membership is right) |
| `AssertError("Attempted to check equality of record:\n[a \|-> 1]\nwith non-record\n2", mv \in {[a \|-> 1]} \cup {2})`, `CONSTANT mv = mv` | TRUE | FALSE |
| `{3, 1, 2} = {1, "a"}` | `Attempted to compare string "a" with non-string:\n1` | `Attempted to check equality of the set {1, 2, 3} with the value:\n{1, "a"}` |
| `Cardinality(UNION {{2, 1}, {"a"}})` | `Attempted to check equality of integer 2 with non-integer:\n"a"` | `Attempted to compare integer 1 with non-integer:\n"a"` |
| `1 \in UNION {{"a"}, {2}}` | `Attempted to check equality of string "a" with non-string:\n2` | `Attempted to compare integer 2 with non-integer:\n"a"` |

The last three under AssertError, with TLC's message, answer FALSE where TLC answers TRUE.

A module instantiated by the name of a module nested in an EXTENDed module fails to parse where
SANY finds it: with `Holder.tla` holding `---- MODULE Held ----` nested, `EXTENDS Holder` then
`J == INSTANCE Held` stops with "Cannot find source file for module Held imported in module M."
(exit 150), where TLC checks the spec. `tests/unit/modules.test.ts` ("sees the nested modules of
an extended module") checks it with the TypeScript check until the front end matches.

A module file holding a UTF-8-encoded surrogate (`ED A0`–`ED BF` and a byte after) reads otherwise
than TLC reads it in the CLI of `dist/`. SANY reads a file through Java's
`InputStreamReader(stream, "UTF-8")` (`TLAplusParser`'s constructor), which replaces each such
three bytes with one U+FFFD, and the CLI's `readFileSync(path, "utf8")` with three. With
`"\xED\xA0\x80"` in a string, TLC prints `Len` of it as 1 and the CLI as 3. Every other sequence
that isn't UTF-8 decodes alike in both (compared over 8,150 sequences of one to four bytes). The
binary's `read_to_string` gives such a file no text and declines it.

A membership in a union whose enumerable side holds a value of another type is TRUE where TLC
fails: TLC tests the enumerable side first, so `ASSUME 1 \in Int \cup {"none"}` stops with
"Attempted to check equality of string "none" with non-string:\n1", where the engine finds the
assumption true and checks the spec. `tests/unit/check.test.ts` ("checks membership in a union of a
non-enumerable set against the enumerable side first") checks it with the TypeScript check.

A function over a domain TLC keeps lazy, applied at one point, fails where TLC computes only that
point: `ASSUME PrintT([s \in SUBSET {1} |-> 1 \div Cardinality(s)][{1}])` prints `1` in TLC, where
the engine computes the function at every `s`, `{}` among them, and stops with "The second argument
of \div is 0." `tests/unit/check.test.ts` ("evaluates a function over a domain TLC keeps lazy only
where it is applied") checks it with the TypeScript check.

A function from strings whose keys are Unicode letters and digits beyond ASCII prints as a function
where TLC prints a record: TLC tests each character of a key with Java's
`Character.isLetterOrDigit` (FcnRcdValue), so `PrintT("x٣" :> 5)` (U+0663, a decimal digit) prints
`[x٣ |-> 5]` in TLC and `("x٣" :> 5)` natively. `tests/unit/check.test.ts` ("prints empty intervals
and keys that are not field names like TLC") checks it with the TypeScript check.

A record TLC compares with itself prints its fields in another order: TLC's equality normalizes the
record, so after `[fld2 |-> 0]` has interned fld2 first, `ToString(LET r == <<[fld1 |-> 1, fld2 |->
2]>> IN IF r = r THEN r ELSE r)` gives `"<<[fld2 |-> 2, fld1 |-> 1]>>"` in TLC and `"<<[fld1 |-> 1,
fld2 |-> 2]>>"` natively. `tests/unit/check.test.ts` ("sorts a record TLC compares with itself and
the records inside it") checks it with the TypeScript check.

A successor whose value fails as TLC fingerprints it is reported as an evaluation failure where TLC
reports a fingerprint failure. With `Filter == {n \in SUBSET {1} : 1 \div 0 = 1}`,
`Next == x' = Filter /\ {} = x'` (or `x' = 1 /\ {1} # Filter`), TLC prints the division, the
behavior, then "TLC was unable to fingerprint." with its Fingerprint Stack Trace and exits 75; the
engine prints the same frames as "The error occurred when TLC was evaluating the nested
expressions" and exits 255. A set TLC keeps lazy that fails to enumerate as TLC fingerprints the
successor does the same with the exit code right: `\E n \in ({1} \cup 2) : x' = n`,
`x' = x /\ \A n \in ({1} \cup 2) : TRUE`, `x' = CHOOSE n \in ({1} \cup 2) : TRUE` and
`x' = Cardinality({n + 1 : n \in ({1} \cup 2)})` print the nested expressions where TLC prints its
fingerprint failure, and `x' \in {1} \cup ({1} \cup 2)` leaves out the last frame of TLC's
Fingerprint Stack Trace. `tests/unit/check.test.ts` ("reports the sources of a set the replay of %s
fails to enumerate", "reports the left side of %s that fails to compare") checks them with the
TypeScript check.

Adding a state to the behavior graph that fails after an invariant violation leaves out where it
fails: with `Fair == x' = 1 \div (x - 1)`, `Next == x < 3 /\ x' = x + 1`, `Inv == x < 2`,
`Spec == Init /\ [][Next]_x /\ WF_x(Fair)` and `PROPERTY Live`, `INVARIANT Inv`, TLC prints after
the trace "The error occurred when TLC was evaluating the nested expressions at the following
positions:" with three frames, and the engine prints the rest alike without it; both exit 12.
`tests/unit/tlc-replay.test.ts` ("prints where adding a state to the behavior graph fails after a
violation") checks it with the TypeScript check.

`RTBound` of TLC's RealTime module, whose body holds `\EE`, applied in an initial predicate, is
declined by the engine (`unsupported: expression UnboundedQuantifier`) and reported by the
TypeScript check as "TLC cannot evaluate an unbounded quantifier at line 20, column 6", where TLC
reports "TLC encountered a temporal formula (\EE) when evaluating a predicate or action." with the
same frames and exit code. `tests/unit/bundled-modules.test.ts` asserts the TypeScript check's
text; it goes with the interpreter.

A file that instantiates or extends its own inner module of the file's name, as `---- MODULE B ----`
holding `---- MODULE B ----` and `I == INSTANCE B` does, declines (`a module that names a module of
its own name`), where TLC checks it: SANY scopes the inner module's context, which the front end
keys by name. It panicked before. It comes back once the front end scopes contexts as SANY does.

The adversarial rounds of the extended file's inner modules and of the library's typed errors
found these, each wrong on main alike:

| Repro | TLC | Native |
|---|---|---|
| A root inner module named `Sequences`, `Naturals`, `TLCExt` or `_TLCTrace`, in TLC's default mode, which writes the trace exploration spec | `Multiply-defined module '<X>'` | checks the model |
| `EXTENDS A, B` where A and B each hold an inner `---- MODULE In ----` | SANY's warning "the declaration of 'In' conflicts with its declaration at …" | no warning |
| `K == INSTANCE B`, B `EXTENDS A` and holds an inner `In`, as A does | `*** Errors: 1`, the multiply-defined module | `*** Errors: 2`, adding "Substitution error, probably due to error in module being instantiated." |
| `EXTENDS B, A` where B instantiates `In.tla` and A holds an inner `In` | `Multiply-defined module 'In'` at A's | checks the model |
| A constant definition `P == PrintT("in")` in a module the spec instantiates | prints `"in"` for the module's definition and again for the instance's | prints it once |
| `P == PrintT("hi")` with a configuration error, such as `NEXT Nope` | prints `"hi"`, then the error | the error alone |
| `CONSTANT K = 3000000000` in the configuration | `NumberFormatException: For input string: "3000000000"` | `Integer overflow` |
| `CONSTANT K <- D` with `CONSTRAINT D`, D a set | `TLC expected a boolean value, but did not find one.` at D's definition | `The constraint of D is equal to {1}` |
| `CONSTANT K <- Nope` where `K` isn't declared and the spec's `C` is unassigned | `The constant parameter C is not assigned a value by the configuration file.` | `In the configuration file, the identifier K does not appear in the specification.` |
| A circular dependency SANY finds as it loads the files, with standard modules to load before the cycle closes | stops at the cycle | parses those modules first, as it finds the cycle once it has loaded every file |
| A constant definition that applies AssertEq, which TLC computes as it starts | `D == AssertEq(1, 2)`: prints `"Assertion failed"`, `1` and `2` | prints nothing (the IR declines TLCExt's builtins there and leaves the definition out of its startup) |
| A decimal an INSTANCE substitutes | `I == INSTANCE Inner WITH c <- 1.5`, unread | checks the model | `TLC can't handle real numbers.` |
| `_POSSIBLE` that lists a predicate twice | `_POSSIBLE AtOne` twice | `Parsing or semantic analysis failed._POSSIBLE: semantic analysis of generated module failed` | `_POSSIBLE lists AtOne more than once` |

The PrintT ones wait on steps 2 and 3 of [startup.md](startup.md). The library's check declines
them ("what the spec prints as TLC computes its constants"): where the front end stops at an error
TLC reports after it computes the constant definitions, and one of those may print
(`may_print_constant_definitions`), and where the engine stops as it starts having left out a
constant definition that applies a TLCExt builtin. The AssertEq one declines there alike. The
library leaves the `Integer overflow` one declined too ("the engine stopped before it searched
(exit 75)").

The front end binds a name to an inner module of an extended file as SANY does
(`resolveNamesBetweenSpecAndExtention`) only where its first load stops at "Cannot find source
file" for the name, every module of the spec has a name of its own, at any depth, and the name
names no file or standard module. There binding by name is SANY's binding by scope. Elsewhere it
reports what it reported before, which differs from TLC where SANY binds the name:

- where the name also names a file or a standard module, it reads that file, where SANY reads none
  and uses the inner module;
- where two modules of the spec share a name, two inner modules or an inner module and a file or
  standard module, it reports "Cannot find source file";
- where a file extends a name bound to an inner module that extends another file, it reports
  "Cannot find source file" too.

Each comes back once the front end scopes an inner module's context as SANY does, instead of by
name; branch `extended-inner-lexical` holds a version that tracks more of SANY's scopes by name.

These print a "states generated" other than TLC's today, outside the corpus and the tests; why,
with TLC's source, is in [lazy-duplicates.md](lazy-duplicates.md):

| Shape | Repro | TLC | Native |
|---|---|---:|---:|
| A held SUBSET or set of functions `\cup` a set that overlaps it | `Init == s = 0 /\ x = 0`, `Next == s' = SUBSET {1} /\ x' \in s' \cup {{1}}` | 10 | 7 |

An adversarial pass on #292 (2,267 specs against TLC at d8fb231, main 40009ac8 and the branch)
found these on main, which the branch prints alike:

| Shape | Repro | TLC | Native |
|---|---|---|---|
| A failing INSTANCE substitute | `N == INSTANCE Inner WITH c <- 1 \div 0`, the substitute used in `Init`, an invariant, a parameterized or unnamed instance | the nested expressions name the INSTANCE and the substitute's own frames | drops those frames |
| A failing conjunct of the specification that is an operator applied to arguments, or an inline LET or LAMBDA | `P(n) == n = 1 /\ Assert(FALSE, "x")`, `Spec == P(1) /\ Init /\ [][Next]_x` | the frames of the body TLC inlines | adds the application's frames first |
| A SYMMETRY definition that prints | `Sym == Print("sym", Permutations(S))` | `The sets "sym", and S have been defined…` | `The sets , and S …` |
| A POSTCONDITION that sets a register | `Post == PrintT(IF TLCSet("exit", FALSE) THEN 1 ELSE 0)` | prints `1` once, then `The post condition Post cannot be a constant.` | prints `1` twice and passes |
| An ALIAS the configuration substitutes a constant definition for | `D == TRUE` (or a record, a set, a tuple, `-1`, a LET), `CONSTANT C <- D`, `ALIAS C` | the alias's value | `_ALIASEvalError = "The alias C cannot be a constant."` (the TRUE case is fixed on the ALIAS branch, alias-trace-fixes) |
| An ALIAS or a POSTCONDITION that is a literal, or that the configuration substitutes one for | `Alias == 3`, `ALIAS Alias`; `Post == "a"`, `POSTCONDITION Post` | `The alias Alias cannot be a constant.` or TLC's message for the postcondition | runs it as a definition (the constant-alias branch's `Definition::LITERAL` fixes it) |
| A configuration substitute scoped to the root module | `CONSTANT C <- [M] E` in the cfg of module M | applies it | ignores it, with another verdict |
| A failing configuration substitute scoped to an instanced module (`<-[Inner]`) | `C <- [Inner] E`, `E == 1 \div 0 = 1`, read through `INSTANCE Inner` | the INSTANCE frame, then the substitute's | the replaced definition's frame |
| A conjunct of the specification the configuration substitutes a FALSE operator with arguments for | `P <- Q`, `Spec == P(0) /\ Init /\ [][Next]_x` | `The spec is trivially false because FALSE is false.` | passes with 0 states |
| A PROPERTY the configuration substitutes an empty `\A` for | `C <- D`, `D == \A i \in {} : FALSE`, `PROPERTY C` | `Temporal formula is a tautology` | passes |
| A violated invariant of an instance inside a PROPERTY | `PROPERTY Prop`, `Prop == [](I!IInv)` | `Invariant I!IInv is violated.` | `Invariant IInv is violated.` |
| An INVARIANT the configuration substitutes a temporal formula for | `INVARIANT C`, `C <- D`, `D == [](x > 0)` | names D, or fails at run time where another invariant reads C | names C, or fails as it starts |
| A tuple or a lexing error in a configuration's value | `CONSTANT K = <<"a">>`, an unclosed string | a lexical error | a parse error, or another position |
| A string where the configuration names a definition | `INVARIANT "a\\b"`, `K <- "a\\b"` | quotes the string | doesn't |
| An ASSUME passing an argument with effects that the operator reads more than once | `Twice(a) == <<a, a>>`, `ASSUME Twice(PrintT("t")) = Twice(PrintT("t"))` | prints once per argument | prints at each read |
| A configuration substitute scoped to an instanced module for a name only it defines | `IK <- [I] IV`, IV defined only in I | `The configuration file substitutes for IK with the undefined identifier IV.` | runs the model |
| A `\*` comment in a configuration with lone carriage returns | a cfg whose lines end in CR alone | ends the comment at the CR | comments out the rest of the file |
| An undefined INVARIANT after a printing constant definition | `D == PrintT("d")`, `INVARIANT Undef` | prints `"d"` first | doesn't |
| An INVARIANT or a conjunct the configuration substitutes an action for | `C <- D`, `D == x' = x` | names D, or `TLC cannot handle this conjunct of the spec: …` | names C, or `TLC cannot handle the action-level conjunct …` |
| A substitute for a definition before it in the module order, unread, defined in an EXTENDed module | `C` in an EXTENDed module, `D == PrintT("d")`, `C <- D` | prints `"d"` twice | once |
| A LOCAL INSTANCE of a module with a printing constant definition | `LOCAL I == INSTANCE N`, `N` has `P == PrintT("p")` | prints twice | once |
| A failing conjunct of the specification that is a TLCEval of a print | `Spec == TLCEval(PrintT(FALSE)) /\ Init /\ [][Next]_x` | prints `FALSE` once | prints it after the violation and the trace again |
| A PROPERTY the configuration substitutes a TLCGet("level") predicate for | `C <- D`, `D == TLCGet("level") > 0`, `PROPERTY C` | no warning | warns of a state-level formula |
| A predicate the configuration substitutes a TLCEval of TLCGet or of a state's Print for | `C <- D`, `D == TLCEval(Print(x, TRUE))` as an INVARIANT, a CONSTRAINT or a conjunct | TLC's message | another |
| A constant INVARIANT that writes TLCSet where TLC doesn't evaluate it | `Inv == IF FALSE THEN TLCSet(1, 2) ELSE TRUE`, or after `TRUE \/`, in an unused LET or argument | warns that Inv is a TRUE constant | doesn't |
| An INVARIANT the configuration assigns a value where the module defines it | `Inv == FALSE`, `CONSTANT Inv = TRUE` | warns and finds no error | warns, then reports `Invariant Inv is violated` |

The engine now declines the shapes that printed other counts here too: a constant definition
normalized elsewhere, then streamed (`C == UNION {1..2, 2..3}`, `Init == s = C /\ x = 0`,
`Next == s' = s /\ x' \in C`: TLC 13, native 17), a stream whose order alone differs from the
normalized set's (`(SUBSET {2}) \cup {{1}}` through a variable, a constant via a variable, a `\E`
name or a LET named twice), and a variable bound by `\in` to a set enumeration's lazy first
element (`Next == s' \in {UNION {1..2, 2..3}} /\ y' \in s'`: TLC 17, native 13).

Outside the counts, SANY's report differs on an INSTANCE of a module with semantic errors: for
`I == INSTANCE Other` with `Other.tla` holding `Op(n) == n - 1` and no EXTENDS, TLC prints
`*** Errors: 2` for module Spec, while the binary prints `*** Errors: 3`, adding `Substitution error,
probably due to error in module being instantiated.` at the INSTANCE (exit 150 in both).

TLC rejects a VIEW or a POSTCONDITION the configuration names by a definition it computed as it
started, as it does an ALIAS, but holds a definition whose body is a number or a string as written
and computes nothing for it (`SymbolNodeValueLookupProvider.lookup`, `Spec.getViewSpec`,
`getPostConditionSpecs`). The binary differs on two shapes: a POSTCONDITION that is a number or a
string, `PC == "s"`, which it rejects as a constant (exit 255) where TLC evaluates it and reports
it not a boolean (exit 10); and a VIEW TLC computes as it starts, `V == TRUE`, `V == {1}`,
`V == A` with `A == 5`, which TLC rejects ("The view function V cannot be a constant.", exit
151) where the binary checks the model.

The binary declines a module file it finds but can't read, such as a directory or text not in
UTF-8 (`a module's file the front end can't read`), where SANY prints `***Internal error: Unable to
create NamedInputStream in toIStream method`. Where the TypeScript check finds the files, TLC's
`SimpleFilenameToStream` still differs from it on:

- `-config _CBORTrace.tla`, which TLC finds among its jar's standard modules and the CLI reports
  missing (the other standard modules decline);
- `-config` naming a resource at the root of TLC's class path, such as `pcal/PlusCal.tla`, after
  which TLC prints a `FileNotFoundException`'s stack trace;
- a `.class` file that isn't one (empty, truncated, `/dev/null` or a socket), which TLC rejects
  with `Found a Java class for module M, but unable to read it`, and a user's `Naturals.class` or
  `TLC.class`, which TLC tries to load;
- under `PROVE_IT_ENGINE=0` alone: options TLC doesn't know, which it rejects.

On Windows, the binary and the CLI find a spec's files by the host's rules (`host_path.rs`), but
print the paths they found as the CLI built them, with `/` between the parts, where TLC prints
Java's: `\` throughout, `File.getAbsolutePath` of a drive-relative path such as `C:Spec`, and
`File.toURI` for the `(file:…)` of a file SANY finds through another path. This is TLC's Windows
path rendering, which neither has ever matched; it waits until it can be recorded against a TLC
run on Windows, since values derived from the JDK's source alone are easy to get subtly wrong.

Proofs: of the 33,025 obligations tlapm's record (`proofs.json`) proves, prove misses 6 on the
record of `prover-inputs.json`, where SMT, Zenon and Isabelle all fail. tlapm proved each with SMT
(prover.md, "Deviations from Z3", has the gate):

| Obligation | `smt` input | Why |
|---|---|---|
| SequencesExtTheorems_proofs #409 | b7775ca0b1b01064 | Z3 4.8.9 proves it, 5.3.3 times out; the port's search is longer |
| Bakery #89 | e67cda013bcdbc0e | the same |
| CRDT_proof #129 | 5390a15510ed57e1 | both Z3s prove it; the port needs 2,570,874 steps, above its limit of 1,321,216 |
| LamportMutex_proofs #574 | cf2bc77dbe72f5d0 | Z3 4.8.9 proves it, 5.3.3 times out |
| PaxosCommit_proof #345 | c4f10dabeaca0a49 | Z3 4.8.9 proves it, 5.3.3 times out; the port needs 10,358,109 steps, above its limit of 7,321,600 |
| Boulanger #240 | b2ca9ee96f3db516 | flattening clauses as Z3 4.8.9 does lengthens the port's search from 1,807,047 steps to 8,170,365, though its 4 distributions are 4.8.9's: open |

These print other than TLC as main does, outside the corpus and the tests; a review of the ALIAS
cells TLC holds as values found them. Each spec has `VARIABLE x`, `Init == x = 0`,
`Next == x' = x + 1`, `Inv == x < 2` and `Q == [y |-> x]`:

| Shape | Configuration | TLC | Native |
|---|---|---|---|
| An ALIAS substituted by a definition the configuration assigns | `CONSTANT Alias <- Q`, `CONSTANT Q = 3` | "The alias Alias cannot be a constant." at each state | the trace through Q |
| An ALIAS assigned a value the front end can't normalize, on a run that prints a trace | `CONSTANT Alias = {1, "a"}` | "The alias Alias cannot be a constant." at each state | the trace through the spec's definition |
| A POSTCONDITION the configuration assigns | `CONSTANT PC = TRUE`, `POSTCONDITION PC` | "The post condition PC cannot be a constant." | another report |
| An ALIAS whose body is a literal, substituted by a module-scoped `<- [M]` in its module, the root, an extended or an instantiated one | `Alias == 3`, `CONSTANT Alias <- [M] Q` | TLC's unexpected ClassCastException | the plain states |
| An ALIAS substituted for a definition of a module both extended and instantiated with parameters, which TLC doesn't compute | `Y <- Alias`, with `Alias == 3` | the plain states | "The alias Alias cannot be a constant." |
| An ALIAS from an INSTANCE with substitutions that the configuration assigns in that module | `INSTANCE N WITH c <- 1`, N's `Alias == [y \|-> c]`, `CONSTANT Alias = [N] 3` | `y = 1` | the plain states |
| A configuration entry scoped to an inner module, which TLC doesn't count as a module of the spec | `CONSTANT F <- [Inner] Alias` | "the module name Inner is not a module in the specification", exit 151 | the trace, exit 12 |

At the level of inputs, #321 also moved ten `smt` inputs tlapm proves from `unsat` to `unknown`
that main proved: 0dfd248d2bdad02b, 12a106a46ac87d79, 181f3f94d6c23221, 2f279b8fcc0984d6,
52c873767bacfb3b, 6181e3d8679eef23, 6f1bb244e72ae33d, 8e48a4022642d1fc, b2ca9ee96f3db516 and
e8e512b5c0878a4e, and gained one. Z3 4.8.9 proves nine of the ten (all but 6181e3d8679eef23). Only
b2ca9ee96f3db516 (Boulanger #240) loses its obligation; Zenon or Isabelle prove the other nine's.

The engine's `decide` declines a text that holds a lone surrogate, so the obligation fails. A string
that is one would read as U+FFFD, two different strings would be one name, and the axiom that they
differ would prove anything. No obligation of tlapm's record holds one.

The SMT solver decides only the SMT-LIB tlapm's encoder writes (`script_subset.rs`). Two known
issues remain within that subset. tlapm's encoder writes neither shape, and no input of the record
reaches either:

| Repro | Z3 4.8.9 | The port |
|---|---|---|
| `(assert (= (* b1 b2 … b12) 1))`, a product of 12 binomials over 24 Int constants | sat at once | runs on: `nlsat::levelwise::add_linear_approximations` reaches `AlgebraicManager::select` and `Rational::floor`, which read neither the deadline nor the step limit |
| `(assert (distinct c0 … c11999))` over `Idv` | not measured | aborts the process: the rewriter's `mk_not` allocates past the size cap, which preprocessing never reads, and an allocation failure isn't caught |

Found porting the unit tests off the interpreter (PR 7), each test case deleted with it, so the
TLC answer the test held is here:

| Repro | TLC | Native |
|---|---|---|
| `ASSUME 1 \in Int \cup {"none"}` | assumption violation | success |
| `PrintT("x٣" :> 5)` | `[x٣ \|-> 5]` | `("x٣" :> 5)` |
| `PrintT` of a record TLC sorts while comparing it with itself and the records inside it | `<<[fld2 \|-> 2, fld1 \|-> 1]>>` | `<<[fld1 \|-> 1, fld2 \|-> 2]>>` |
| a function over a domain TLC keeps lazy, applied only where defined (`\div 0` elsewhere) | success | the assumption fails: "The second argument of \div is 0." |
| an error in a module nested in a nested module | SANY's errors | SANY's errors and "A VARIABLE declaration may not appear within a recursive definition section." |
| an ALIAS field holding a lazy function that fails to apply | the field's lazy text, `[i \in 1..1 \|-> <expression …>]` | `_ALIASEvalError` "The second argument of \div is 0." in each state |
| an exception TLC raises printing a state of a violation | 2110 with no states, then 1000 "Attempted to compare boolean TRUE with non-boolean:\n1" | 2110 with both states, no 1000 |
| `onProgress` of a spec whose INSTANCE adds definitions TLC warns about (EXCEPT warnings, check.test.ts "computes the definitions an INSTANCE adds…") | three warnings, at Cases lines 4, 6 and 5 | none, from the library or the CLI |
| `onProgress` of a state-level PROPERTY before a CONSTRAINT equal to FALSE | the `state-level-property` warning for P, then the error | the error alone |

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
| The engine stopping where TLC reports an error | 48 | 27 | memo session |
| What the constant evaluator doesn't compute | 14 | 3 | front session |
| Other failures evaluated again | 29 | 18 | memo session |
| The engine declining an operator or builtin | 14 | 11 | memo session |
| Print and PrintT where the engine can't place them | 16 | 4 | S1 (lazy-values) |
| `-dump` (`dot`, and under SYMMETRY or a VIEW) | 12 | 3 | S2 |
| Java overrides TLC loads with more than the shapes ported | 9 | 8 | unassigned |
| SANY's report of RECURSIVE declarations | 4 | 3 | XML session |
| The rest: a configuration substitute with effects, states TLC may take for the search's under VIEW or SYMMETRY, and a trace the search can't step | 4 | 3 | unassigned |

The groups are checked in this order, so a decline counts once, in the first group that takes it.
The constant evaluator's row and the Java overrides' row count what was left after the
front-constants branch (measured 2026-11-11 from b8121dd3, 1,452 native before and 1,473 after):
it made native the CHOOSE, division, equality, quantifier-bound and INIT or NEXT constant
declines, and an annotated override and one that catches, and moved TLCGet("level") as a
substitute to "a configuration substitute with effects" among the rest.
The startup checks after it (measured 2026-11-11 from ee6736a4, 1,499 native before and 1,512
after) made native the SYMMETRY definitions TLC fails on, the configuration error that shows a
set, the successor TLC fails to find again from its generator, and the constant invariants TLC
warns about, but one that overflows TLC's stack and one that fails as a set operation. The
constant conjunct of the specification that draws at random moved to the engine's decline of
RandomElement under a comparison.
The TLCExt builtins after it (measured 2026-11-11 from 924d7cde, 1,478 native before and 1,482
after) made native AssertEq, UNCHANGED in the initial predicate and PickSuccessor where TLC answers
without asking, and moved TLCGetAndSet's run and the interactive PickSuccessor to the engine's
stops.
The 1.7.4 runs leave with the TypeScript, and `check-log` now counts them apart, as retired with
the interpreter, without running them. The other 438 block deleting the interpreter, with native
progress events for the library's `onProgress` (see "The public API afterwards").

#### Declines to win back

Checks the binary answered and now declines, because the answer matched TLC only by chance.

- **The library where the check stops before it searches without a typed error** (PR 7): a
  decimal or big literal the front end rejects, and a big number in the configuration, which it
  words otherwise than TLC or rejects where TLC doesn't (see "Known wrong outputs"), and a stop
  after SANY printed a warning, which the library would print before it throws. The binary prints
  its output, but `get_thrown` returns nothing, so `check` throws `TlaUnsupportedError` "not
  native yet: the engine stopped before it searched (exit N)" where the interpreter threw its own
  error. Won back: SANY's fatal errors (a module it can't find or parse, a file named after
  another module, a circular dependency), which `check` throws as `TlaSyntaxError` with SANY's
  report; and the other configuration and evaluation errors TLC reports before it searches (a
  configuration file it can't parse, a SYMMETRY that isn't a set of permutations, a temporal
  formula it can't handle or whose constant part fails, a stack overflow, an exception as it
  starts), which `check` throws as `TlaConfigError`, `TlaEvaluationError` or
  `TlaStackOverflowError` with TLC's message, after what the spec printed as TLC computed its
  constants. 205 of the 214 such errors `bun run test` throws are TLC's error and prints, run
  against TLC at d8fb231; the others are listed under "Known wrong outputs", or are TLC's warnings
  TLC prints before the error, which `onPrint` doesn't get, or TLC's call stack after a stack
  overflow, which `TlaStackOverflowError` doesn't hold.

- **Strings made during the search** (the string-order change; check-log on the same log, 1386
  native on main, 1384 after): `unit/check.test.ts:704` and `unit/parallel.test.ts:18` with
  `-workers 2`, both `fixtures/strings/RuntimeStrings`, where `CHOOSE` picks among
  `"q" \o ToString(n)` strings the search makes. TLC orders two strings by when it interned them,
  and it interns a string the search makes as it makes it. The store ordered two that no rank covers
  by their text, which matched TLC's creation order there by chance. It now stops on them (`an order
  of strings the search made`), and the library's tests assert TLC's output through the interpreter.
  Winning them back takes the engine ranking what it makes in TLC's order of evaluation: one worker,
  every successor and every expression in TLC's order, which a later change would have to show.
- **Live progress during a native check.** The native check reports `onProgress`'s events once it
  ends, where the TypeScript check reported them as the search reached them. Live delivery would
  take a callback the check calls as the printer prints: a threadsafe function in the napi binding,
  since the check runs on its own thread, and an import in the WebAssembly binding. `checkSources`
  reruns the check from the start each round it needs another file, so the events of a round may
  go out only once it is the last: the library would hold them until the check returns without
  asking for more, or the check would ask for every file before it searches.

### After the FingerprintException burn-down (measured 2026-11-11)

Measured at #272 (main 924d7cd merged) with `bun scripts/run.ts check-log`:

- 1,895 checks. 1,495 print TLC's output natively and 400 are not native yet, for 147 reasons,
  listed in full under "Every reason" above. None answered differently on one thread and four.
- The declines TLC words as a FingerprintException went from 69 runs to 3: "values TLC can't
  compare" (2) and "equality of values TLC can't compare" (1).
- In TLC's default mode, which writes the trace exploration spec, 1,044 are native.

SANY's report of RECURSIVE declarations is native from #266, which takes SANY's messages from
its generator where linking declines. Measured with `check-log` at that PR's head 04c7267: none of
the 4 runs declines; of 1,891 checks, 1,456 are native and 435 not native yet, with 0 answered
differently on one thread and four, and 1,020 are native in TLC's default mode.

### Java overrides that stay declined

The front end reads the class TLC loads for a module and puts the constant each method returns in
place of the operator. It skips a method annotated `@TLAPlusOperator` or `@Evaluation`, as
`processModuleOverrides` does, and runs a method that catches an exception up to its first return.
It declines an annotated method where a `tlc2.overrides.TLCOverrides` index, beside the spec or at
its package's path, could load the class. These shapes stay
declined for good, because what TLC does with them depends on the JVM, not on the class file:

- **A static initializer, a field's initializer or a superclass.** Java runs them as TLC first
  calls a method, and what they print or throw shows in TLC's output. A failure there is an
  `ExceptionInInitializerError`, whose report holds the JDK's own stack frames.
- **A value the method computes by calling the JDK,** such as `Integer.parseInt`, which the front
  end would have to run as Java does.
- **Several methods TLC reports.** `Class#getDeclaredMethods` lists them in the order HotSpot
  allocated the symbols of their names, which changes with `-Xshare:off` on the same JDK, and TLC
  prints a message for each in that order. Where two methods share a name, the one listed last
  overrides the other. The binary declines a class whose methods print more than one message, or
  that has methods of one name, wherever the order could change what TLC logs.

A method whose name `TLARegistry.mapName` maps to an operator's, such as `Plus` to `+`, is declined
for now, not for good: the standard modules whose classes register the names are those SANY
parsed before the overriding module, which in TLC's default mode include the modules of the trace
exploration spec. With `-noGenerateSpecTE` and no EXTENDS, TLC at d8fb231 loads `Plus` as `Plus`,
and in the default mode it fails to match it as `+`.

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
- **Native progress events (done).** The native check records each message TLC prints, with its
  code, its place among the spec's prints and, for a check of the temporal properties part way
  through the search, the search's counts; `check` turns them into `CheckProgress` events
  (`src/native-progress.ts`), which it reports once the check ends. On the corpus models the native
  check answers, the events and their order equal the TypeScript check's (746 of the 762 it answers
  of 920; of the other 16, six were the report of a violation, fixed since, five the clock's, one
  a warning below, and four differed in the result or the prints: TLC's recordings side with the
  native check on Github696b's error and VoteProof's deadlock, where the TypeScript check differs,
  and the two UserModuleOverride models printed what the property prints as TLC finds the behavior
  violating it only through the TypeScript check, which the native check's `onPrint` now
  receives too), but for
  the events TLC schedules by the clock: natively a caller gets a `progress` event for each report
  the native search made, every minute, and a `liveness-started` with `isComplete` false for each
  check part way through it, at the native search's own times. Where the two differ otherwise:
  - `liveness-initializing` takes `isSymmetric` and `isConstrained` from the configuration, as
    TLC warns, where the TypeScript check first drops a constraint that is a constant formula and
    a symmetry whose sets are too small;
  - a name the configuration lists twice gets the warning event TLC prints, which drops a warning
    identical to one it printed (`MP.printWarning`), where the TypeScript check reports it twice;
  - with `-nowarning`, the native check reports none of the warnings TLC doesn't print, where the
    TypeScript check still reports a constant-level invariant, a state-level property and a
    symmetry set too small;
  - what the native engine doesn't print yet has no event either: the warning of an EXCEPT on a
    record's missing field in an ASSUME or an ALIAS, and what the spec prints as TLC searches for a
    liveness counterexample;
  - `PROVE_IT_TEST_LIVE_CHECK_AT` names the state before whose expansion the native search checks,
    and after whose expansion the TypeScript check does.
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
- **The library's answer.** Where the engine as WebAssembly stops at its bound
  (`recursion deeper than WebAssembly's stack holds`) or traps, the library's check throws
  `WebAssemblyStackError`, which names the addon and the binary, rather than search again in the
  interpreter. So a model that recurses between 1,000 and 20,000 calls is checked with the addon
  and the binary and rejected as WebAssembly: `native.test.ts` pins both answers.

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
default natively. After an error trace of two states or more it writes the spec TLC writes,
`<Spec>_TTrace_<epoch>.tla`, and its path after `Finished in` (`te_spec.rs`), and for any
counterexample the trace file, `<Spec>_TTrace_<epoch>.bin`, which is identical where TLC reads it
back to the same trace (AGENTS.md, "The oracle"; cli.md, "-dumpTrace"). On the 733 corpus models in
TLC's default, against TLC's recordings of that mode, with each `.bin` compared by what the jar
reads back from it, 723 print and write what TLC does, 3 differ as they do with
`-noGenerateSpecTE`, by TLC's runtime (a Java stack overflow, where TLC is installed, and a
NullPointerException in TLC), and 7 decline at a trace file `tla-trace` doesn't dump: a random
draw, whose trace TLC may not find again for its postconditions (5), a set TLC keeps lazy (1), and a
deadlock that violates a temporal property (1).

### The public API afterwards

`check` and its option, progress, result and status types, `prove` and its types, `parseConfig`,
and the errors stay. `parseModule` and `Module` are the front end's to decide.

`Value`, `formatValue` and the values in `TraceStep` and `Violation` were the interpreter's
classes. The owner decided to break them, and they broke after the CLI's flip:

- `check` runs `checkSources` as the CLI does, with the spec and its configuration as the files
  `<Module>.tla` and `<Module>.cfg`, its modules through `loadModule`, and `-seed`, `-workers`,
  `-lncheck`, `-tool`, `-nowarning` and `-continue` from its options. The Json module's operators
  read and write the library's files there, through `readFile` (`read:<path>`) and `writeFile`
  (`Settings::json_files`): the engine reads what the library read for it before the search, and
  stops at a file it hasn't, which the library reads before the check runs again, so a check that
  reads a file only as it searches searches twice; it keeps what they write, which the library
  writes once the check ends, each file with what it was last written. The machine's `isLibrary`
  says so, and only then does the check write each printed state's plain
  data, at most 1,000,000 elements of it a variable, TLC's own bound on a set it builds; past
  that the value is `null`. The binary and the CLI's `checkSources` write none.
- The check records what it found as it prints (`prove-it-check`'s `outcome.rs`), and
  `checkSources` returns it as `outcome` (ABI 16): the status, the counts of TLC's statistics, what
  the spec printed, and each violation or error TLC reports, as its message's code and text with
  the states TLC prints after it. A state carries each variable as TLC prints it and as plain data.
- Where the native check stops before it searches, at a spec or configuration TLC rejects,
  `checkSources` returns the error the library throws for it as `thrown` (ABI 27), with what the
  spec printed before it, which the library prints first: a `TlaSyntaxError` with SANY's report
  (`createSanyError`), a `TlaConfigError` or a `TlaEvaluationError` with TLC's message, or a
  `TlaStackOverflowError`. Where the library can't know all TLC prints before the error,
  `checkSources` declines (see "Known wrong outputs"). Before ABI 27 `thrown` held only a
  `TlaConfigError` of tla-front's config error and a `TlaEvaluationError` for a temporal formula
  TLC can't check or a spec with no next-state action. SANY's report holds the errors of the
  first module with errors and the warnings so far, which the TypeScript check throws. The library
  left the error to the TypeScript check where the two may differ:
  - a fatal error of SANY's parsing phase, as the TypeScript check loads modules as it links them;
  - a module with a literal TLC can't hold, which the TypeScript check rejects as it loads it;
  - the arity of an instance's substitution, and a module defined twice, which it words its own
    way or doesn't report;
  - other evaluation errors, which it throws as its subclasses or not at all;
  - a stop after SANY or the spec printed, and a configuration or evaluation error in a spec that
    may print as TLC computes its constants (one that names `Print`, `PrintT`, TLCExt or IOUtils,
    or loads a Java override), which it prints first.
- Where the native check declines, stops before it searches without `thrown`, or the options ask
  for what only the TypeScript check does (`onPause`, a `dump` as `dot`, TLC 1.7.4), the
  TypeScript check runs and its result converts (`src/check-result.ts`). A `ModelConfig` goes to
  the native check as the configuration file that holds it (`formatConfig`), and a plain `dump` as
  `-dump`, whose file `checkSources` returns among its `writes` for `writeFile`.
  `systemProperties` go to the native check as a Java launch's `-D`, as the binary reads them.
- `Value` and `formatValue` are no longer exported.
- A set or function TLC keeps lazy is `{"@lazy": text}`, with TLC's `toString` of it, which the
  trace printer writes exactly as it writes the states (`tests/fixtures/plain-lazy` pins it against
  TLC's output). Where the text can't be TLC's, a value is `null`: a set TLC can't normalize
  natively, and in the interpreter a lazy function or filter it has no source for.
- `onPrint` gets what the spec printed once the native check ends, not as it prints. What the spec
  prints as TLC rebuilds a trace isn't in the result.

Of the 387 calls of the library's `check` in `bun run test` at the change, 199 ran natively. Of
the 188 others, 114 stopped before the search, 44 were declined and 30 asked for the TypeScript
check. The tests of the interpreter's own results run `checkParsed`, the TypeScript check. With
`thrown`, 104 of the 115 calls at 9cd662c6 that stop before the search throw the TypeScript check's
error natively, and 11 leave it to the TypeScript check.

### What changes for users

- `PROVE_IT_ENGINE=0` goes. Where no engine loads, `EngineUnavailableError` has no escape hatch:
  - WebAssembly fails to compile;
  - or `dist` lacks the engine.
  A browser keeps the WebAssembly engine.
- A WebAssembly stack overflow is an error, `WebAssemblyStackError`, in the library's check. The
  PR that removes `PROVE_IT_ENGINE=0` drops its message's clause that names it.
- `-dump`, `-continue` and periodic configs are checked natively. TLC 1.7.4's output is retired.
- The library prints what the binary prints. Today they differ only where the library hands over.

## -coverage in the engine

The engine's search doesn't count TLC's cost model; the replay pass in `tla-trace` does
(cli.md, "-coverage"). Counting in the engine was built (branch `engine-coverage`) and not adopted:
TLC with coverage runs 20 to 35 times as long as the engine's search on record-heavy specs, so the
times of TLC's report part way through can't be bounded from the engine's.

## tlapm

`prove-it tlapm …` runs natively (`prove-it-check`'s `tlapm.rs`): in the binary, and in the CLI of
`dist/`, which hands the command line to `checkSources` and applies the file operations its result
lists (`prove-it-host`'s `files.rs`). There is no TypeScript fallback: where the native command
declines, the CLI prints the decline and exits with 1, and where no engine loads, it throws
`EngineUnavailableError`. A run either prints and writes what tlapm does or declines as a whole:
both hold back what the run prints and writes until it ends (`prove-it-check`'s `overlay.rs`).

### What matches

- Every fixture tlapm 9ed0376 recorded in `tests/fixtures/obligations` and `tests/fixtures/tlapm-cli`
  (`prove-it-cli/tests/tlapm.rs`, `unit/cli.test.ts`): stdout, stderr and the exit status, with
  `-N`, `--toolbox`, `--line`, `--printallobs`, `--strict`, `--summary`, `--nofp`, `--cleanfp`, and
  over tlapm's own fingerprints file; the theory file byte for byte; and the fingerprints file,
  which holds what tlapm's holds but for each result's date and versions. tlapm copies Zenon's
  stderr to its stdout, and the native command writes Zenon's `exhausted search space` line, which
  the deleted TypeScript CLI left out. It sends Isabelle's stdout to a file (`Prep.isabelle_prove`), and
  Isabelle writes nothing to stderr for a proof it doesn't find, so such a failure prints as any
  other.
- `scripts/tlapm-conformance.ts` on the 1,873 modules of `tests/conformance/tlapm.json`, run as
  `record-tlapm.ts` ran tlapm (`-N --printallobs --toolbox 0 0`): every one of the 33,138
  obligations of the 1,507 modules tlapm accepted prints byte for byte, and the 366 modules it
  rejected decline.

### Declines

- **What timing decides** (`Schedule.run`): tlapm launches every decision it can, up to
  `--threads`, before it takes any result, and takes each as it comes back. Where two are in
  flight together, either can come back first, and the run declines where that changes what tlapm
  prints or writes: in toolbox mode, where each prints a message as it comes back (`toolbox
  messages of two decisions in flight at once, …`); a thunk still to be evaluated of an obligation
  with the fingerprint and prover of a decision in flight, which reuses its result or not as it
  comes back first or not; an SMT encoding still to be made that numbers CASE errors, whose count
  the order changes; Zenon's notes of different texts and Isabelle's proofs of different
  obligations, which tlapm writes as they come; and different results for one fingerprint and
  prover, of which the fingerprints file keeps the last. With one thread, or where one decision is
  in flight at a time, the order is tlapm's.
- **An error tlapm ends with** (`the backtrace tlapm prints as it ends with …`): tlapm prints the
  exception with the OCaml backtrace of where it raised it, and in toolbox mode a toolbox message of
  the location and message `Errors.set` kept (`tlapm_lib.ml`, `init`). Neither is known without a
  run of tlapm, and the recordings in `tests/fixtures/obligation-errors` leave the backtrace out. A
  module file that isn't there declines the same way. The deleted TypeScript CLI printed these without the
  backtrace.
- **What a back end writes that tlapm copies to its stdout.** tlapm runs each back end with its
  stderr on its own stdout (`System.launch_process`). Zenon's is known (`Zenon error: …`, from
  `prove.ml`'s `periodic` and `prove_fail`) and written. The native command declines:
  - a Zenon search that stops otherwise than on an exhausted search, the memory limit or the time
    limit, and an input a back end can't read.
- **What Prove It can't try as tlapm does:** a method with no back end in Prove It, and a method
  whose encoder can't take the obligation (`smt can't encode …`), where tlapm would try it. tlapm
  has no back end for Cooper either: it fails the method and warns `Cooper's method is not
  available any more.` on stderr (`Prep.prove_with`), which Prove It doesn't print yet. Where
  tlapm can't run cvc3, the error it prints holds the machine's PATH.
- **Command lines it doesn't model:** an option outside `src/cli/options.ts`'s list,
  `--printallobs` where tlapm proves (tlapm then prints each proved obligation's text too), an
  option without its arguments or without an integer (as OCaml's `int_of_string` reads one, with
  `0x`, `0o`, `0b` and `_`), a negative `--threads` (`Tlapm_args.set_max_threads` raises
  `Arg.Bad`, proving or not), `--threads` 0 or above 99 where tlapm proves (its scheduler
  asserts), and so a machine of more than 99 processors without `--threads`, no module, and
  globs. tlapm reports each in its own words, after a `--version` before it prints the version. An
  empty `-I`, and `-I +dir` where tlapm's standard library isn't found, end tlapm abnormally.
- **What `Loader` reads as tokens** (`what comes before the module header of …`): tlapm finds a
  module as `M_save.file_search'` does, in the current directory, each `-I` directory in the order
  given and its standard library, naming it by that path (`./M.tla`, `I1/M.tla`), or else through
  `Loader`, beside the command line's modules, naming it by its file's name alone. `Loader` hands
  the lexer the text, which it reads in token mode from the start rather than from the header on,
  so a module it reads with more than blanks and comments before its header declines.
- **A byte that isn't UTF-8 where the obligations hold it** (`a byte that isn't UTF-8 outside a
  comment in …`, naming the first module read that holds that byte): tlapm reads bytes, and read
  with U+FFFD for each such byte, two different strings would be one and a theorem that they are
  equal proved. Both the binary and the CLI read a module's bytes (`bytes:` keys) and decode them
  in `prove_obligations::bytes`: each byte that doesn't start a well-formed sequence (Unicode's
  Table 3-7) reads as a marker of its own, U+10FF00 plus the byte, the same for each byte value
  everywhere. The run declines where the obligations (everything they hold), a warning or an error
  hold a marker; elsewhere, as in a comment, before the module's header or past its end, it prints
  and proves what it would with U+FFFD. A module whose UTF-8 holds a character from U+10FF80 to
  U+10FFFF, which it would read alike with a byte, declines (`U+… in …, which Prove It reads a
  byte that isn't UTF-8 as`). Columns count bytes, as tlapm's do (`Loc`, `pos_cnum - pos_bol`),
  each marker one.
- **A cache it can't read or write as tlapm does:** a fingerprints file that doesn't load (tlapm
  moves it aside). Where tlapm can't make its cache directory or a module's in it
  (`Tlapm_lib.mkdir_tlaps`, a `Unix.mkdir`, which makes no directory above it), or write the
  fingerprints file, as where a directory is there, it ends abnormally with a backtrace (`the
  backtrace tlapm prints as it ends where it can't write …`). An empty cache directory, from
  `--cache-dir ""` or `TLAPM_CACHE_DIR=`, has tlapm make each module's directory at the root, which
  Prove It doesn't do. Where the file system refuses an operation the run's reads let it expect,
  as a directory under `/proc`, the binary and the CLI decline once the run ends (`a directory
  tlapm can't make: …`, `a file tlapm can't write: …`), with the operations before it applied.

### Declines to win back

Runs the deleted TypeScript CLI printed as tlapm does only by chance:
- Toolbox mode with more than one thread, where two decisions are in flight together: the
  TypeScript printed each obligation's messages in order, which tlapm does only where the results
  happen to come back in that order.
- A method Prove It can't encode the obligation for (`smt can't encode …`) or has no back end for:
  the TypeScript left the method out, which printed what tlapm prints only where tlapm's attempt
  also failed and nothing printed it, as outside toolbox mode.
- A byte that isn't UTF-8 in a string the obligations hold but neither print nor prove, such as a
  theorem of a module the module extends: read as U+FFFD, the theorem was never read.

### Known wrong outputs

- `tlapm/test/fast/language/parse_function_comma_args.tla` #2: Prove It's SMT encoder writes the LET
  definitions inside the LET, and the SMT back end proves the obligation, where tlapm's
  `Smtlib.pp_print_expr` writes them outside it and Z3 rejects its input
  (`scripts/tlapm-deviations.ts`). tlapm reports a failure and Prove It a proof.
- An obligation a back end decides otherwise than tlapm's, within the same time limit, prints the
  other status. Run with `--threads 1 --toolbox 0 0` on the 248 modules of `proofs.json` with at
  most 120 obligations, against the statuses tlapm recorded there (measured 2026-11-12): 242 give
  every obligation tlapm's status, 5 decline (two `smt can't encode a temporal formula`, one `smt
  can't encode the operator Print`, cvc3 and Cooper), and 1 differs,
  `parse_function_comma_args.tla` #2 above. With more threads, a module where two decisions are in
  flight together declines in toolbox mode.
- A carriage return alone ends a `\*` comment for tlapm's lexer (`alexer.mll`'s `newline`), and
  not for the front end's, which reads the rest of the line as the comment.
- A TAB before the module header, on the header's line, shifts the columns printed on that line,
  because the front end expands tabs and tlapm counts bytes.
- tlapm writes each proof Zenon finds to the theory file (`Prep.save_result`, `Isabelle.thy_write`),
  with Zenon's input and the command it ran on a temporary file; Prove It's theory holds
  Isabelle's proofs alone.
- tlapm warns, on stderr or as a toolbox warning, where it reuses a proof found with a longer time
  limit than the method's (`Prep.already_processed`'s `success_warning`), which Prove It doesn't.
- tlapm prints `status:being proved` in toolbox mode for a decision that has run for `--wait`
  (3 s) (`Prep.mk_timec`), and stops launching others until then, which Prove It doesn't do.
- The toolbox header's command line is Prove It's, `prove-it tlapm …`, as tlapm prints its own
  (`tlapm_args.ml`, `init`); no recording holds tlapm's.
- The binary and the CLI of `dist/` print what the command printed once it ends, not as it goes.
  The binary keeps the order in which the run wrote to stdout and stderr; the CLI writes stdout,
  then stderr. Where both go to one file, neither need interleave them as tlapm, whose stdout is
  buffered, does.
