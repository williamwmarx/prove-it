# The native binary, as built

Notes on `prove-it-cli` as it is built, after `native/DESIGN.md` §13.7, which has the first
ones. The plan stays in §13.

## The check as a library

The binary's check lives in `prove-it-check`, which `prove-it-cli` runs on stdout and stderr: it
writes what TLC prints, and its own notes such as `not native yet`, to an `Output`, so that the
host can run the same check in-process ([fallback.md](fallback.md), S1). A printed value whose
text depends on how TLC built it used to end the process at once. Now the check prints nothing
more, and its relay cancels the search (`Reporter::is_cancelled`). The engine asks where it checks
its progress: every 256 states on one thread, and after each share of a level on several. The
search declines within that, and the check reports the model as not native, with the same output
and exit code.

What a decline leaves printed:

- **The binary prints as it checks.** A decline found while it checks the initial states or a
  definition prints none of TLC's report of the initial states. A decline found in the next-state
  relation comes after that report. Either way the binary has printed only TLC's own lines, up to
  and including that report. Then it writes `prove-it: not native yet: <reason>` to stderr and
  exits 1.
- **The library and the dist CLI print none of it.** `checkSources` returns `declined` without what
  the check printed (`prove-it-host/src/check.rs`). The CLI's per-call fallback then checks the spec
  in the interpreter, whose output stands alone (`src/cli/tlc.ts`).
- **The tests hold the binary to this.** `prove-it-cli/tests/lazy_duplicates.rs` records which
  cells decline after the initial states (`not native yet after the initial states`). A declining
  cell prints nothing after that report, and only those cells print it.

## The library's check

The library's `check` runs this check through `checkSources` and reads the outcome it records as
it prints ([fallback.md](fallback.md), "The public API afterwards"). The outcome comes back once
the check ends, so `onPrint` gets what the spec printed then, in order, and not as the spec prints.
What the spec prints as TLC rebuilds a trace, before or between its states or after it, is in the
binary's output but not in the library's result.

## Print and PrintT (#66)

- `Reporter::print` hands the CLI the printed values as ids of the search's store; the N-API relay
  encodes them for JavaScript as before.
- The binary writes each value with `tla_values::print` and breaks it as TLC's `tlc2.pprint` does
  (`pretty.rs`, a port of `src/pretty-print.ts`, checked against it on 208 generated values).
- A value `is_printable` refuses ends the run as not native.
- The differential's count went from 542 to **586 of 1466** runs.

## TLC's actions in the IR (#72)

IR 5 always carries TLC's actions with the label a trace step gets (`getActionLabel`), and an
`is_labelled` flag. They are found only where nothing the spec's description evaluates has an
effect (a random choice, a TLC register, Assert, printing). Elsewhere the IR has none, since
finding them would change what the run does.

## An invariant an initial state violates

- The engine's `SearchOutcome::Stopped` carries a `Violation` when it knows what TLC reports:
  - for now `ViolationKind::InitialInvariant`;
  - the violating state's values;
  - the store they live in, so the CLI prints them with TLC's printer.
- Invariants are checked as deduplicated conjuncts. `EngineContext::invariant_owners` names, for
  each, the first configured invariant it belongs to. Checked in order, the first conjunct that
  fails belongs to the first violated invariant in the configuration's order, which TLC names.
- The CLI prints message 2107 with the state in TLC's variable order, prints no statistics, and
  exits 12.
- It reads the configuration with `tla-front`'s parser. Under an ALIAS, TLC prints the alias, which
  the IR doesn't carry, so the run is not native.
- A state is printed only when `is_printable` (the strict check) holds for every value. TLC sorts a
  record's fields by `UniqueString` intern order and normalizes every state it fingerprints. That is
  the order the store keeps, so Walgit's `manifest = [logSegments |-> {}, headSeq |-> 0, ...]` is
  in store order, not written order (the trace session found this). The normalized check
  (`is_printable_normalized`, #74) will fit fingerprinted states. A state TLC doesn't fingerprint
  (outside a CONSTRAINT or ACTION_CONSTRAINT) waits for the trace evaluator.
- The search passes on what the spec printed before the violation, but only when the caller reports
  violations itself (`Settings::is_violation_reported`). Under N-API the interpreter starts over
  and prints everything again. A POSTCONDITION or POSSIBLE keeps a violation not native, since TLC
  checks those on the trace after it prints it.
- Measured on Depot: 600 of 1466 runs print what TLC prints, up from 586. Nothing new differs.

## Deadlock and invariant traces

- `ViolationKind::Deadlock` and `ViolationKind::Invariant(owner)` carry the path of states to the
  last one, with the violating successor the search didn't keep. They also carry `labels`, the
  position in `model.actions` of each step's action, from `label_path` (#79). `label_path` also
  labels a step to such a successor. A step no action takes keeps the run not native.
- `StopCounts` are the counts check.ts reports at the stop. Generated includes the violating
  successor. Distinct counts it when it is new. Queued is the states found less those expanded.
  Depth includes the successor's level when it is new.
- The search finds the actions only when the binary asks (`is_violation_reported`) and labels
  are worth it. That means nothing prints (a trace's rebuild would print again), there is no VIEW
  or symmetry (TLC prints the states it rebuilds, not their representatives), and there is no
  graph. A store with strings the search ranked (ToString) gives no violation either (#82).
- The CLI prints 2110 `Invariant X is violated.` or 2114 `Deadlock reached.`, then 2121 and a 2217
  per state (`N: <label>`, `<Initial predicate>` first), then the statistics and depth, with
  progress first under -tool. It exits 12 or 11.
- Measured on Depot: 650 of 1466 runs print what TLC prints, up from 600. Nothing new differs.
  Most remaining deadlocks and invariant violations print records, which wait for #74.

## The startup phase (DESIGN 14.3)

The engine runs TLC's startup on the IR before its search (`run_startup`, `search.rs`). Until
then, the TypeScript environment evaluated TLA+ before the search and wrote the values into the
IR. The front end evaluates nothing (F8 agreed the boundary), and `tla-front` returns `NotYet` for
a model that needs an item below that the engine doesn't take yet.

IR 11 carries `model.startup`, which `ir.ts` writes from `check.ts` and `tla-front` will write the
same way:
- **substitutes**: each a declared constant's name and the 0-ary definition the configuration puts
  in its place, where that definition isn't of constant level. TLC evaluates it at startup
  (`SpecProcessor.processConstantDefns`), and reports 2281 only where that fails and the level is
  above constant. The engine declines a model whose substitute fails, for now.
- **definitions**: the constant definitions TLC evaluates at startup that have effects (`Print`,
  `RandomElement`, `TLCSet` and the like), in the order TLC evaluates them. A definition without
  effects is the same wherever it is first evaluated, so the engine computes it there. Each is
  compiled once with an empty footprint. The engine declines one TLC may keep lazy (`may_be_lazy`),
  as TLC then evaluates it again where it is used.
- **symmetry**: the SYMMETRY definition, and each set its body's operator applies to, by the name
  TLC's warning gives it (`getPermutedSets`, `symmetry.ts`) and, for `Permutations(S)` of a
  constant or definition the configuration doesn't replace with `<-`, S. TLC evaluates the body
  again as it builds its `Tool` (`Tool.getSymmetryPerms`), after the constant definitions and
  before the assumptions. The engine builds the group (`close_group`), and declines a value that
  isn't a set of functions of model values, or a body TLC may keep lazy, which TLC may reject. It
  hands the group to the interpreter and `tla-trace` by the model values' names
  (`Checkpoint.symmetry`, `Rebuilder::set_symmetry`).
- **assumptions**: each one's expression and the name TLC reports it by (`describeRange`).
- The settings carry TLC's seed, from which the engine draws what the startup draws
  (`JavaRandom::seeded`), and then reseeds for each state as before. `TLCGet("level")` is 0 at
  startup.

What the engine reports (`Reporter`):
- `startup_print`: each `Print` and `PrintT` of the substitutes, definitions and symmetry, then
  `symmetry_sets_too_small` with the sets TLC warns about (2300), then `startup_done`, then what
  the assumptions print. The front prints TLC's own text between them:
  TLC prints what it prints itself after the constant definitions and before it checks the
  assumptions (`ModelChecker`, then `checkAssumptions`).
- `SearchOutcome::AssumptionViolated { name }`: the first false assumption (2104, exit code 10).
- An assumption that fails to evaluate (2105), and any other `Bail` at startup, declines the model
  before anything is reported, so the interpreter that takes the model over prints it all once.
- Through the addon, the interpreter has already run the startup, printed what it printed and
  checked the assumptions before it hands the search over. The addon's reporter keeps the default
  `startup_print` and `startup_done`, which do nothing, and declines an assumption the engine finds
  false. The binary (`prove-it-cli`) declines it too, until it prints the startup itself.
- `Checkpoint.startup` and `Violation.startup` carry the definitions' values, so the interpreter
  and `tla-trace` (`Rebuilder::set_startup`) read the values the search read rather than draw again.

Still to do:
- **Multi-module order.** TLC runs `processConstantDefns` per module, in its module table's order:
  each module's substitutes, then that module's constant definitions, then its inner modules. The
  IR lists all the substitutes and then all the definitions, as `evaluate.ts` evaluates them. The
  two differ only where printing or drawing definitions sit in more than one module along with
  substitutes. No corpus model has been found that shows the difference; one that does is a
  TypeScript bug to fix on both sides, not a design choice.
- **The small-set warning of a body that isn't an operator application.** TLC counts the
  arguments of any operator application, `IF` included, as the permuted sets, and names each by
  its text. `getPermutedSets` reads only an `Apply`, so for `Sym == IF c THEN Permutations(S)
  ELSE {}` TLC may warn where TypeScript and the engine don't. That is a TypeScript bug to fix on
  both sides.
- TLC's actions (`getNextActions`, `spec-description.ts`): the engine is to split Next itself and
  label each action. Then the effect guard on TLC's actions (#72) goes away, which unblocks native
  traces for specs that print (etest3, etest8).
- A configuration constant with arguments (`createOperatorTable` in `environment.ts`) needs no
  evaluation: the front end can write its rows of literals in a section `operator_tables`, and
  the engine formats them with TLC's printer for the two errors it raises.
- Action labels read `specification.instanceActions`, which `tla-front` fills from linking. A scope
  binding holds a `Value` only from the action split, which moves to the engine.
- `getActionLabel` depends on the TLC version (1.7.4 or later); the IR already carries the version.

## Temporal properties that hold (#134)

- A model that records the state graph goes through the native search. When the search completes
  and the engine's liveness check says the properties hold, the binary prints what check.ts prints
  once the Rust backend reports `holds`:
  - `Progress(depth)` without rates, the counts at the end of the search with 0 left on queue
    (`liveness-started`, `isComplete`);
  - 2192 `Checking [N branches of ]temporal properties for the complete state space with
    branches × distinct total distinct states at (…)`;
  - 2267 `Finished checking temporal properties in … at …`;
  - then the summary, as for any search.
- A counterexample stays not native ("a temporal property's counterexample") until the binary
  prints it with the trace evaluator's states and labels.
- Measured on Depot: 798 of 1466 runs print what TLC prints. That count includes main's own gains
  since #84. Of the 264 temporal runs, 132 remain counterexamples. Nothing native differs.

## A temporal property's lasso

- When the liveness check finds a lasso and the binary reports violations itself, the search's
  `Complete` outcome carries it as a `Violation` of kind `Lasso { loop_start, loop_label }`: the
  lasso's states, the action of each step (`label_lasso`), the counts and the store. Under SYMMETRY
  or a VIEW the stored states aren't the ones TLC prints, so there is none.
- The binary prints what `printViolation` prints for a `liveness-violation` with a `loopStart`:
  - the Progress line and 2192, as for properties that hold;
  - what the spec printed as TLC rebuilt the whole trace, which it rebuilds before it reports;
  - 2116, naming the violated properties as `getTemporalHeadline` does;
  - 2264 and each state (2217);
  - `Back to state N: <label>` (2122 with -tool), or `N: Stuttering` (2218) where the cycle is the
    last state alone;
  - 2267, then the statistics and exit code 13.
- Still not native:
  - a stuttering counterexample TLC warns of under a SPECIFICATION (2259), which names where the
    specification is defined. Without one, the binary prints TLC's 2257 warning after the
    `Stuttering` line;
  - a lasso whose cycle steps back to an earlier state in a spec that prints, since TLC prints as it
    finds that step's action;
  - an accepting node, which TLC reports as it builds the behavior graph.

## Temporal checks part way through the search

- As TLC does unless `-lncheck final` (or `seqfinal`, `off`), the binary asks the engine to check the
  temporal properties as the search goes (`is_liveness_periodic`, #148). For each check it prints
  2192 `Checking [N branches of ]temporal properties for the current state space with
  branches × expanded total distinct states at (…)`, with no Progress line before it, and 2267 once
  the check finds that the properties hold so far, as check.ts does for the engine's
  `liveness-started` and `liveness-finished`.
- PROVE_IT_TEST_LIVE_CHECK_AT sets the number of expanded states after which the first check comes,
  as for the TypeScript CLI, so a test can reach one on a small model.
- A counterexample a check part way through finds stays not native: the interpreter prints it with
  the counts so far.

## Step labels from the rebuilt trace

- The binary labels each step of a trace with the action `tla-trace` finds as it rebuilds the
  trace (`TraceState.action`, #139), as TLC's `Tool.getState` does, not with the search's own labels.
- So the search hands over a violation's trace wherever the caller reports it:
  - under VIEW or SYMMETRY, whose stored states aren't the ones TLC prints;
  - in specs that print, where finding the actions would print again;
  - where the search can't find a step's action.
  In those cases each step's label is `None` and the rebuild tries TLC's actions in turn.
- Still not native:
  - a step whose action the rebuilt trace lacks, as in a model whose IR has no actions (etest3), whose
    label is the whole next-state relation's range;
  - a trace the rebuild declines, such as RandomElement and RandomSubset, or the several states
    one symmetry orbit may give TLC.

## ALIAS

- With an ALIAS, the binary prints each state of a trace through it, as TLC does. `tla-trace`'s
  `Rebuilder::alias` evaluates it on the rebuilt trace, with the next state TLC gives it: the
  following state, or for a lasso's last state the state its cycle starts at. The binary prints the
  record's fields in the order TLC prints them, a line each, as a conjunction when there are
  several.
- An alias whose value isn't a record leaves the state printed as it is. What the rebuild can't
  follow, such as an alias that fails or prints, stays not native.

## The front, from tla-front

- tla-front is the binary's only front end (`front.rs`): it prints SANY's report as
  `tla_front::report::get_sany_text` writes it and lowers the model with
  `tla_front::model::lower_front_ranking`. The lowered IR has no TLC actions; the trace evaluator
  splits Next (`tla_trace::add_actions`).
- `files.rs` names the files SANY parses as `createFileDescriber` does. The directory TLC copies
  a module into is named by TLC's fingerprint of a string, as `getTemporaryName` does it.
- The differential used to hand the binary a recorded front (`PROVE_IT_FRONT`: the IR and the
  text the TypeScript CLI printed before the search). It is gone; the one test seam left
  is `PROVE_IT_TEST_IR`, which names a golden engine IR the CLI tests check in place of the
  lowered one, with no SANY report and nothing printed before the search but the engine's
  startup.

## POSTCONDITION

- The IR carries the configuration's POSTCONDITIONs (`Model.postconditions`). `tla-trace`'s
  `Rebuilder::postcondition` evaluates each one, with TLCGet("all:named")'s `_POSSIBLE` counts,
  TLCGet("stats") and, after a violation, CounterExample built from the rebuilt trace.
- After a search that completes, the binary prints what the postconditions printed as TLC
  evaluates them, then the first that doesn't hold, in place of the success:
  - 2404 `Postcondition X at <body range> is false.`, or
  - 2405 `Evaluating postcondition X at <body range> failed.` with TLC's message;
  then the statistics, and exit code 10.
- After a violation, what the postconditions printed follows the trace, and a failing postcondition
  is reported after the step back into a lasso's cycle. The violation's exit code stands.
- Still not native:
  - a postcondition TLC computes as it starts, which it rejects;
  - an unwitnessed `_POSSIBLE` predicate after a violation (the violation carries the counts as
    the search left them, `Violation::possible`, which a witnessed one checks with);
  - what `Rebuilder::postcondition` declines, such as CounterExample's actions with parameters.

## -dumpTrace

TLC dumps a violation's counterexample with postconditions of its trace modules, which it parses
with the spec: `_TLCTrace` for `-dumpTrace tlc` and the trace exploration spec's
`<Spec>_TTrace_<epoch>.bin`, `_JsonTrace` for `-dumpTrace json`. Each writes
`[counterexample |-> CounterExample, vars |-> vars]`.

The binary (`prove-it-check`'s `dump_trace.rs`) does what TLC does with `-dumpTrace tlc <file>` and
`-dumpTrace json <file>`:

- `args.rs` reads `-dumpTrace <format> <file>` as `handleParameters` does: the flag and the format
  in any case, any number of times, the two arguments after the flag whatever they are, with TLC's
  messages for a missing pair and an unknown format. `tla`, `tlcplain`, `tlcTESpec`, `tlcaction`,
  `dot` and `cbor` stay not native: their modules import the CommunityModules
  (`checkDumpTraceModules`).
- TLC adds each format's module to the root module's EXTENDS in the order of the options, and the
  trace exploration spec's `_TLCTrace` after them where it records the trace
  (`ParameterizedSpecObj`). The binary gives tla-front the same list (`Files::root_extendees`,
  `ModelOptions::root_extendees`), so SANY's report, the order TLC interns strings in, and Integers'
  methods over Naturals' are TLC's. `_JsonTrace` brings `Json` and its modules as TLC lists them.
- The postconditions run where the binary already checks the configuration's after a violation, and
  before them (`getPostConditionSpecs`): after an invariant's or an action property's violation, a
  deadlock, a temporal property's lasso, after the step back into its cycle, and an initial state's
  violation of an invariant or a property, after the state. TLC builds the counterexample as
  `Worker.doPostCondition` does (`Rebuilder::rebuild_counter_example` for a violation it holds).
  Each writes its file in argument order, relative to the working directory, and prints
  `"CounterExample written: <file>"`, as PrintT does, plain and with -tool. A run without a
  counterexample writes and prints nothing more.
- The modules share their constant (`_TLCTraceFile`, `_JsonTraceFile`), which TLC sets for each
  postcondition in turn (`processConstantsForModule`), so each option of a format writes, and
  names, the file of the last of that format: `-dumpTrace tlc a.bin -dumpTrace tlc b.bin` writes
  `b.bin` twice and never `a.bin`.
- `to_tlc` takes the configuration's model values (`ModelConfig::get_model_values`).

Not native: where TLC also records the trace (its default without `-tool`, `-noTE` or
`-continue`), a counterexample, whose `.bin` the trace exploration spec's postcondition writes with
the same constant; a failure evaluating the spec past the initial states, after which TLC may check
the postconditions on a trace it can't find again; a spec that draws RandomElement or
RandomSubset, whose trace TLC may not find again, writing nothing; a deadlock that violates a
temporal property; a file name that isn't printable ASCII or holds a quote or a backslash; a file
in a directory that doesn't exist; `-dumpTrace` with `-continue`; a configuration POSTCONDITION TLC
rejects, as TLC then writes no dump (it collects every postcondition before it checks any,
`Spec.getPostConditionSpecs`); a module of the user's that a
trace module uses, such as a `Json.tla` beside the spec, which SANY loads in place of the standard
one, failing TLC's run in `_JsonTrace`'s analysis ("Unknown operator: `JsonSerialize'.") where
it lacks what `_JsonTrace` uses (SANY's report of the extra modules declines it as it does for the
trace exploration spec's `_TLCTrace`); and what `dump_trace` declines.

`tests/dump_trace.rs` holds the binary to what the jar (tlaplus d8fb231) printed and wrote, with
`-tool` and without, both orders of the two formats: an invariant violation, a deadlock, a lasso, an
initial state's violation and a run without a counterexample (`tests/dump-trace`).

Swept (2026-11-11) over the 721 corpus models whose recorded TLC run with -tool took at most 10 s,
each run by the jar and the binary from a working directory of its own with
`-tool -modelcheck -dumpTrace tlc A.bin -dumpTrace json A.json`: stdout normalised, the JSON byte for
byte and the `.bin` but for its tokens. 609 match (71 of them writing both files), 110 decline, 2
differ as they do without -dumpTrace (a jar path TLCGet reads, and TLC's stack overflowing), and
none differ otherwise. The declines: a substitute made again (45), a failure evaluating the spec
(25), an argument or a LET definition made again (24), an ALIAS (7), a random draw (5), an action's
parameter (3), and a deadlock that violates a temporal property (1). Without -tool and with
`-dumpTrace json` first, over the 174 that stop at a counterexample: 88 match, 85 decline, 1
differs as it does without -dumpTrace.

- `Rebuilder::dump_trace(&CounterExample) -> Result<TraceDump, Unsupported>` builds the value, with
  `Rebuilder::rebuild_counter_example(store, states, labels)` giving an invariant violation's trace
  as TLC holds it then (`Worker.doPostCondition`): the states rebuilt, and the last found again
  among the successors of the state the search held, so the two share no value but those TLC made
  once, such as a string literal's.
- `TraceDump::to_tlc(model_values: &[&str]) -> Result<Vec<u8>, Unsupported>` is the gzipped file
  (`_TLCTrace.ioSerialize`): the value fingerprinted, which sorts it in place, then written by
  `ValueOutputStream`'s grammar, back-references to the values written before included. A value
  written twice is one `Rc` of the evaluator, as it is one Java object to TLC: a string literal is
  one object per node, a state's unchanged variable is its predecessor's. `model_values` are the
  configuration's in the order `ModelConfig.parse` makes them, whose positions TLC writes. The gzip
  member has `GZIPOutputStream`'s header and stored deflate blocks.
- `TraceDump::to_json() -> Result<String, Unsupported>` is `Json.serialize`'s text, Gson's
  escaping included: records and functions in the order written until TLC sorts them, so a JSON
  dump after `to_tlc` writes them sorted, as TLC's does when `-dumpTrace tlc` comes first.
- The payload equals TLC's but for the tokens of its strings (`design/gaps.md`), which the dump
  numbers in the order it first writes each text. `tests/dump.rs` compares the dumps of four specs
  with what the jar (tlaplus d8fb231) wrote, in both orders of the two flags: an invariant
  violation, a deadlock, a lasso, and nested values.
- Round trip: the jar read each of the eight `.bin` files `tla-trace` wrote and its own with
  `java -jar tla2tools.jar -tool -modelcheck -config <Spec>.cfg -loadtrace tlc trace.bin <Spec>`,
  and printed the same, but for times, pids, the seed and the fingerprint index: the trace
  replayed, exit 12, 11, 13 and 12.
- Not dumped (`Unsupported`): a safety violation of a model with an ALIAS; a set or function TLC
  keeps lazy, whose cached enumeration is a Java object of its own; an action's parameter bound to
  a string, set or function, the object its set holds, which a state may hold too; a model value
  the configuration doesn't make. The sharing follows the evaluator's, which these specs check; where
  TLC's state queue spilled the held state to disk and read it back, TLC's literals are new
  objects, which the dump doesn't follow.
- The corpus sweep found where the evaluator's sharing wasn't TLC's, now followed:
  `[S -> T]` enumerates a lazy `T` once for each element of `S` (`SetOfFcnsValue.Enumerator`), so
  no two arguments share a value; SubSeq and SelectSeq give TLC's one empty sequence
  (`TupleValue.EmptyTuple`) and `\o` gives back the other operand where one is empty; DOMAIN of a
  record makes new strings (`RecordValue.getDomain`). And where it isn't, declined
  (`Evaluator::unshared`): an argument or a LET definition evaluated again to a value with an
  identity, which TLC keeps for a next state (`LazyValue`), and a constant the configuration
  substitutes a definition for, which TLC evaluates at each use while the evaluator keeps one value.

## Specs TLC stops at before the search

- tla-front finds whether TLC stops before it searches, and the binary prints what TLC prints
  then:
  - SANY's report, framed by 2220 "Starting SANY..." and 2219 "SANY finished." under -tool;
  - 2185 `Starting... (…)`;
  - SANY's rejection of the spec (3002, exit 150), or the error tla-front's lowering raises with
    TLC's code and exit code (`FrontError::get_coded`: configuration errors with 151, evaluation
    errors with 75, a stack overflow with 255, and TLC's `errorConstantToExitStatus` by code:
    2146 with 76, 2253 with 77, 2213 and 2214 and an unexpected exception with 255);
  - then 2186.
- A configuration file `parse_config` rejects is reported the same way, right after the banner, as
  TLC reads it before it parses the spec.
- Lowering reads modules beside the spec, then from each `-DTLA-Library` directory in order.
- Where tla-front doesn't find where TLC stops, the not-native reason says why.

## What TLC prints as it starts

- The binary prints SANY's report as tla-front writes it (framed by 2220 and 2219 under -tool),
  then `Starting...`, and lowers the model itself. What TLC prints as it starts comes from the
  engine's startup hooks:
  - `startup_print` prints as `Relay::print` does, with the same `is_printable` check, so a value
    whose text depends on how TLC built it stops the run as not native;
    Where the store has forgotten how TLC built a value, the binary takes what the substitutes,
    constant definitions and configured definitions print from the trace evaluator
    (`Rebuilder::startup_prints`), so long as each print the store words is the same and there
    are as many; not under SYMMETRY, whose body the evaluator doesn't evaluate;
  - `symmetry_sets_too_small` prints 2300 as `Tool.getSymmetryPerms` words it.
- Not native when this was first measured, as TLC prints more as it starts (front.md has what
  has landed since):
  - the Java overrides TLC loads (any `.class` file beside the spec);
  - the warning of a constant-level invariant (2149), which the IR drops;
  - a PROPERTY: the warning of a state-level property and the tableau's branches (2212);
  - the trace exploration spec TLC parses with the spec, unless `-tool`, `-noGenerateSpecTE`
    (`-noTE`) or `-continue` (`isTraceRecorded`).
- The binary seeds TLC's generator with -seed, which tla-front's IR doesn't hold.
- `differential --native <binary> --native-only` runs the binary alone this way.
- Measured (2026-11-09) on the TLC test models of up to 5 s: 462 of 758 runs print what TLC
  prints with no recorded front, and none differs once the seed is set. What only this path
  declined then:
  - a PROPERTY (244 runs, 122 models): TLC's warning of a state-level property (2255,
    `getProperties`), the warning of symmetry with liveness (2279), and 2212 `Implied-temporal
    checking--satisfiability problem has N branches.`, with N the tableau's solutions
    (`Tableau::solutions` on the IR's `live_formula`), all in TLC's order after 2300 and before
    the assumptions. The state-level check needs a property's level, which tla-front knows
    (`get_properties`) and the IR doesn't carry;
  - an assumption's print whose value the store forgot (SetPredValue): it needs the trace
    evaluator's prints of the assumptions, with a check of their count where the search starts;
  - Java overrides (UserModuleOverride): TLC's report of the class it loads (2168, or 2400
    where a method matches no operator).

## AssertError assumptions

- AssertError compares TLC's message for a failure, which the engine doesn't word. Under
  `compiler.is_native` it compiles to a failure `DELEGATED_ASSUMPTION`, and an assumption that
  fails with it is left to the caller (`Reporter::check_assumption`): the binary checks it with
  the trace evaluator (`Rebuilder::check_assumption`), after the startup and the assumptions
  before it, with -tool or without, since under -tool a message TLC raises with a code holds the
  code's markers. The engine takes TLC's generator from where the check left it and checks the
  assumptions after it itself.
- Still not native: an AssertError assumption that fails to evaluate, sets a register, or follows
  the configuration's predicates or a SYMMETRY, and AssertError anywhere but an assumption.
- The corpus models with AssertError assumptions are blocked elsewhere:
  - ModuleSemanticsAssume: `RandomSubset` in an operator's argument doesn't compile (the argument
    may not print);
  - EmptySetEqAssume (`{<<>>} = [{} -> Nat]`) and RandomSubsetEmpty: the engine fails on an
    assumption TLC finds true, which the replay catches ("it didn't fail");
  - ValueSemanticsAssume: the replay enumerates an infinite set the engine failed on.

## The command line

`args.rs` reads the arguments as `TLC.handleParameters` does, in order, and stops at the first one
TLC rejects with TLC's message (1102 and the usage line, marked only where `-tool` came before it):
an option TLC doesn't know, a missing or malformed value of `-seed`, `-workers`, `-fp`, `-config`,
`-lncheck` or `-metadir`, a `-dumpTrace` without a format and a file or with a format TLC doesn't
know, and, on the `tlc2.TLC` form, a second module or none. Each message was
compared with a TLC built from the clone at d8fb231.

It models `-config` (with or without `.cfg`, as TLC), `-continue`, `-coverage`, `-deadlock`,
`-dump`, `-dumpTrace tlc` and `-dumpTrace json` (below), `-fp`, `-lncheck`, `-metadir`, `-modelcheck`, `-nowarning`, `-seed`, `-tool`, `-workers` and the
trace-spec switches (`-generateSpecTE [nomonolith]`, `-noGenerateSpecTE`/`-noTE`,
`-noGenerateSpecTEBin`/`-noTEBin`), and `-simulate`, `-depth` and `-aril` (below). Every other
option TLC reads (`-generate`, `-difftrace`, `-maxSetSize`, `-dfid`, ...) is not native, as are the
shapes where TLC
throws (`-dump` last, an empty argument), an argument that isn't ASCII, and `Spec.cfg` named as
the module on the `tlc2.TLC` form. `-lncheck off` is not native either: TLC then checks no temporal property (`LiveCheck.java:238`).
`-fp N` picks `FP64.Polys[N]`, one of TLC's 131 irreducible polynomials, which every fingerprint
extends from: of the states, which the search keys its table on, seeds each state's draws with and
measures the "actual fingerprints" estimate by, and which order the liveness checker's tables; of
TLCFP's values and TLCCache's keys; and `TLCGet("config").fingerprint`. Each polynomial's table is
built the first time it is used. Without `-fp`, TLC picks a polynomial at random, and the binary
picks the first, as `-fp 0`: the "actual fingerprints" estimate it prints is then polynomial 0's,
where TLC's varies from run to run.
`seqfinal` is `final` with one worker for the liveness check (`LiveCheck.java:291`), so the two
read alike.

`-workers N` (or `auto`, every core) is the number of threads the search shares its levels and
the liveness checker's atoms between, at most the cores ([parallel.md](parallel.md)). They find
what one thread finds, so the binary prints what TLC prints on one worker, whatever `-workers`
says; only the banner names N workers, as TLC's does. TLC on N workers may find another
counterexample or report a greater depth, as its workers don't keep to levels.

On the `tlc2.TLC` form a system property in TLC's namespaces (`-Dtlc2.…`, `-Dutil.…`,
`-Dtla2sany.…`, `-Dtlc.…`) is not native, except the two that only reach the execution statistics
TLC reports home and change nothing it prints: `tlc2.TLC.ide` (`TLC.java:1710`, `REPL.java:275`)
and `util.ExecutionStatisticsCollector.id` (`ExecutionStatisticsCollector.java:74`, `205`).

`TLCGet("-Dname")` reads a system property with the key as the default
(`TLCGetSet.java:485`). The engine answers the key for a name nothing sets and the platform's
`file.separator` and `path.separator`, and declines any other name in the JVM's own namespaces
(`java.`, `os.`, `user.`, ...) and a key the spec computes. The binary declines a command line
that sets a property whose `-Dname` the model's strings hold, since the spec may read it.
The TypeScript CLI carries the launch's properties into the run (`systemProperties`), with the
platform's separators and `user.dir`, and fails as unsupported on another of the JVM's own.

`prove-it <Spec>...` without `tlc2.TLC` stays Prove It's own
form (DESIGN 13.1): several specs, `Spec.cfg`, and its usage where none is named.

## -dump

`-dump <file>` writes each state the search found to `<file>.dump` (TLC adds the suffix where the
name lacks it), as TLC's `StateWriter` does: `State N:` from 1, the state as TLC prints it
(`TLCStateMut.toString`), and a blank line. TLC writes a state as it adds it to its set of
fingerprints, before it checks the invariants, so on a stop the dump holds the states the
stopping expansion found and the state that stopped it where TLC counted it. The engine hands the
states over once, as the search ends (`Reporter::dumped`, `Settings::is_dumped`), and the binary
opens the file where TLC does, before it reads the configuration, so a run that stops before the
search leaves it empty. Each run was compared with TLC's dump at d8fb231 over the corpus.

With N workers TLC writes the states in the order its workers happen to add them, which differs
from run to run. The binary's shared levels find what one thread finds, so its dump on any number
of workers is TLC's dump on one worker.

Not native, where TLC writes what the binary doesn't model:

- `-dump dot ...` (`DotStateWriter`), `-dump class,...` and a file under `${metadir}`;
- temporal properties: TLC writes each state again as it adds its stuttering step to the behavior
  graph (`Worker.doNextCheckLiveness`);
- SYMMETRY or a VIEW;
- a search stopped computing its initial states: TLC returns without closing the dump (no
  `cleanup`), which then holds only what Java's buffers flushed;
- an invariant that fails to evaluate past the initial states: TLC expands the state again to
  print the call stack and writes the new states it finds then (`keepCallStack`);
- a spec with no variables, and a state holding a value whose text depends on how TLC built it.

## -continue

Under `-continue` TLC reports each invariant and action property violated and goes on: the
binary prints each as TLC does, without TLC's trace spec, which `-continue` turns off
(`isTraceRecorded`), and ends with the statistics of a search without a violation and exit 0
([gaps.md](gaps.md)). The search runs on one thread, whatever `-workers` says, so it finds the
violations in the order TLC's worker finds them. Checked against TLC's ContinueTest,
DoInitFunctorInvariantContinueTest and ContinueSuccessors, and the corpus run with `-continue`.

## -coverage

`-coverage N` prints TLC's coverage report (2201, the lines, then 2202) where TLC's `printSummary`
prints it, after the trace and before the statistics, plain and with `-tool`. The states, traces
and statistics still come from the engine's search; the report comes from a pass after it in
tla-trace (`coverage/`), which reruns TLC's breadth-first search at one worker as TLC's `Worker`
runs it: the initial states with their invariants, the queue first in first out with its spills to
disk (`DiskStateQueue`, whose read-back values hold no cost model), the actions in TLC's order, the
constraints, the fingerprints, the invariants and the deadlock check, stopping where TLC stops, and
the trace TLC rebuilds for a violation. It counts where TLC's cost model counts: a tree built as
`CostModelCreator` builds it over SANY-shaped expressions of the IR, the evaluation of
`Tool.getInitStates`, `getNextStates` and `eval` with `LazyValue` caching and the cost model each
value carries (enumerations and conversions count as secondary counts), and each variable's
`HyperLogLog(10)` estimate of the values in the queued states, with `-fp`'s polynomial, or without `-fp` with each of TLC's. The pass
returns the states it generated and found, which must agree with the engine's. It declines
anything it doesn't follow exactly, and the run is then not native; it never prints a report TLC
wouldn't. Each line was compared with TLC's at d8fb231.

Not native:

- more than one worker: TLC's workers share the cost model and race on it. Five runs of a model of
  three actions at `-workers 4 -coverage 1` printed five different reports.
- a report part way through the search: TLC prints one after a progress report every N minutes
  (`AbstractChecker.runTLC`, `count = coverageInterval / progressInterval`, counted down after
  each progress report; `ModelChecker.runTLCContinueDoing` reports where it is 0), so at the first
  progress report, about 3 s in, for `-coverage 0`, and at the (N + 1)-th for `-coverage N`. When
  the engine reaches that progress report, the relay cancels the search (`Event::CoverageReported`).
  The progress TLC prints as it computes the initial states and the checks of temporal properties
  don't count down.
- a run TLC may take more than 5 minutes over (below).
- temporal properties, properties TLC checks as invariants or actions, SYMMETRY, VIEW,
  `_POSSIBLE`, POSTCONDITION, a run that ends other than at its end, an invariant violation or a
  deadlock, definitions an INSTANCE copies, and a long tail the sweep tallies below.

### 2777 rather than 2202

`CostModelCreator.report` (`tool/coverage/CostModelCreator.java:433-446`) ends the report with
2777 (`TLC_COVERAGE_END_OVERHEAD`) rather than 2202 where more than 5 minutes passed since
`startTime`, which `TLC.process` sets after reading the arguments and before SANY
(`TLC.java:1194`), the start the "Finished in" time is measured from too. That is TLC's own wall
time, which depends on the JVM and the machine, so the binary can't know it. What it can bound:
the binary with coverage took at least 3.45 times as long as TLC with coverage on every model of
the perf suite that runs long enough to measure (table below: 3.77, 4.0 and 3.45), the pass alone
being slower than TLC; on a model that checks in moments both are dominated by starting up, the
JVM's seconds. So a native run of at most 60 s, measured from the same point (the `start` the
binary times "Finished in" from, before the configuration and the front), implies a TLC run of
about 60 / 3.45 = 17 s plus the JVM's start, a margin of more than ten times under 5 minutes.
Past 60 s the binary declines the report.
`PROVE_IT_TEST_COVERAGE_CUT` sets the cut in seconds for tests, so they don't depend on the
machine's speed.

The cut also ends before TLC's first report part way through, which comes 3 s after its workers
start for `-coverage 0` and every 60 s after, at 3 + 60·N s for `-coverage N`
(`AbstractChecker.runTLC`'s `wait(3000)`, then each progress report): the cut is the lesser of
60 s and that time. Before, a `-coverage 0` run of a few seconds printed one report where TLC
printed one part way through too. The bound is the binary's time, not TLC's, so a `-coverage 0`
run the binary takes more than 3 s over declines even where TLC's search would end within 3 s.

The cut rests on the pass being slower than TLC, which does TLC's value work. Counting in the engine
was built and not adopted: on models full of records TLC with coverage runs 20 to 35 times as long
as the engine's search, so no native time of the engine's bounds TLC's report part way through
(branch `engine-coverage`, closed PR #307).

Two more declines:
- Under `-continue`, a run carried past a violation: TLC counts Init and Next again as it rebuilds
  each violation's trace, which the pass doesn't, and where an initial state is violated the
  binary printed no report where TLC prints one.
- Without `-fp`, a report whose estimates differ by polynomial: TLC draws one of its 131 at
  random (the banner's `fp`), and two values hashed to one register of its `HyperLogLog` change
  the estimate, so its report differs from run to run. The pass keeps each variable's distinct
  values and estimates them with every polynomial; the report is native only where all 131 agree.

### Sweep and performance

The corpus models TLC checks in 10 s or less, run by TLC's jar and the binary with `-workers 1
-coverage 1 -noGenerateSpecTE -fp 0`: 259 match (189 print a report; the whole output matches for
all 259), 456 decline and none differ. A sample of 63 with `-tool` matched. The declines: temporal
properties 127, a run ending otherwise 58, SYMMETRY 35, the engine's constant invariants 35,
INSTANCE 33, no variables 30, an operator taking an operator 17, properties checked as invariants
17, VIEW 12, `_POSSIBLE` 10, a lazy set filter 8, ENABLED 7, a state holding a lazy set 7, and
fewer than 6 each for the rest.

Wall time in seconds, TLC with `-workers 1 -coverage 1`, the binary without and with `-coverage`:

| Model | Generated / distinct | TLC | Engine | Binary with -coverage |
| --- | --- | --- | --- | --- |
| 2PCwithBTM | 5,841 / 1,245 | 2.3 | 0.1 | 0.1 |
| MCLamportMutex | 2,729,079 / 724,274 | 28.8 | 4.4 | 108.5 |
| MCExactInitialSync | 39,107,880 / 9,610,407 | 320.9 | 26.2 | 1,284 |
| PaxosCommit | 16,959,159 / 1,321,761 | 296.9 | 38.1 | 1,023 |

The other models of the suite decline: MCbtree (an EXCEPT of a function of several arguments),
TLCSailfish1 (INSTANCE), MCabs and BufferedRandomAccessFile (SYMMETRY), GameOfLife (a lazy set
filter), MCMultiNode (an operator taking an operator), Detlefs and FastPaxos (SYMMETRY), StarkMutex,
cf1s_folklore and SpanTreeRandom (temporal properties). The pass, a tree-walking replay, runs at
about a quarter of TLC's speed. The approved follow-up counts the cost model in the engine's own
search, which would retire the replay.

## -simulate

`-simulate [num=N]` runs TLC's random simulation (`Simulator`, `SimulationWorker`) in the engine
(`tla-engine/src/simulate.rs`), on one worker, drawing what TLC draws in its order, so a run with
the same `-seed` and `-aril` takes TLC's traces and prints TLC's output:

- `TLC.process` seeds a `RandomGenerator` with `-seed` (0 without one, where TLC draws a seed),
  skips `-aril` draws of `nextDouble` (only with `-seed`), and draws the worker's seed with
  `nextLong`; the worker seeds its own generator with it.
- A trace starts at an initial state drawn by `floor(nextDouble() * n)` among the initial states
  in the model, in the initial predicate's order, duplicates kept.
- Each step draws an action index the same way, then `nextPrime()` (a `nextDouble` index into the
  1341 primes from 1277011), and walks TLC's actions from that index, striding by the prime modulo
  their number, until one has successors in the model. The successor is drawn by
  `floor(nextDouble() * n)` among them in the walk's order.
- Every successor the walk completes counts as checked and is checked against the invariants,
  then the action properties; it is kept where the constraints and action constraints hold. A
  state with no successor kept is a deadlock unless `-deadlock` (or `CHECK_DEADLOCK FALSE`).
- A trace ends after `-depth` steps (100 by default; `-depth -1` has no bound) and adds
  `min(depth, level)` to TLC's integer Welford mean and squared deviations, packed in one long as
  TLC keeps them, which the progress line prints.
- RandomElement and RandomSubset draw, past the startup and the initial states, from a generator
  of the worker's thread seeded with `-seed` and never reseeded (`RandomEnumerableValues`).
- TLCGet("level") counts the trace's steps, stuttering ones too; TLCGet("config") is the
  simulation's record (`Simulator.createConfig`). Any other key of the run declines, and so does an
  assumption left to the trace evaluator in a spec that reads TLCGet, which it answers as the
  model checker.

The report: the banner `Running Random Simulation with seed ...`, `Computed N initial states...`,
`Finished computing initial states: K distinct state generated` (no plural), then for a violation
its headline and the trace without its finite stuttering (`getTrace`), each state labelled with
its action, the first with the last of TLC's initial predicates (`initial_label`, which
tla-front finds as `initPredVec`); with `-depth -1` the error state alone. Then the summary
(`The number of states generated`, the seed and aril) and the final progress line, in TLC's order.
`getTrace` drops a state equal to the one before it, from the last state back, comparing the
values in TLC's order of the variables up to the first that differs, which fails where TLC can't
compare them (TLC's Github743). A trace's states print from the store where no value's text depends
on how TLC built it, and else as the trace evaluator rebuilds them along the actions taken, unless
a state holds a record of several fields: the evaluator sorts its fields as TLC's fingerprints do,
and the simulation fingerprints no state, sorting a record only where it happens to compare it.

Declined, each with its reason:

- several workers; `-generate`; `file=`, `stats=` and `sched=`;
- `-coverage`, whose report TLC's simulator prints too (`Simulator.reportCoverage`), where the
  coverage pass replays the model checker's search;
- `-dumpTrace`, a postcondition TLC's simulator checks as it checks the model's;
- temporal properties (TLC's `LiveCheck1` per trace), POSTCONDITION, `_POSSIBLE`, SYMMETRY,
  `_PERIODIC` (evaluated with each progress report), a model without a next-state relation or
  whose relation the engine doesn't split into TLC's actions;
- a violation before the last trace, or without `num=`: TLC's worker goes on generating traces
  as the main thread prints the trace, and is stopped at no particular one, so the counts race.
  In one run of an MCConsensus model on the jar, the summary said 23 states generated where the
  progress line, printed after it, said 24. The sweep declines 60
  runs for this; the tests pin `num=1`, where the violation is in the last trace;
- a failure evaluating the model, an incomplete state, an action property violated, an initial
  state outside a constraint or none;
- a violation under `-continue`, after which TLC's simulator goes on generating traces
  (`TLCGlobals.continuation`) and exits with 0;
- a trace the trace evaluator can't rebuild, such as one that drew at random under an ALIAS, or
  that holds a record of several fields where the store can't print it;
- a temporal formula TLC's model checker rejects as it builds its liveness checker (a tautology),
  which the simulation builds only as it checks a trace.

## Handoff

- tla-front feeds the search, or reports where TLC stops before it (above). Parity measures the
  binary that way: `differential --native-only --native <binary>`, gated on
  known-differences.json's `tlc/native` entries.
- Sweep for wrong output after a big push: list the corpus models whose configuration uses
  SYMMETRY, VIEW, ALIAS, POSTCONDITION(S) or `_POSSIBLE`, and run
  `bun scripts/run.ts differential --compare-backends --filter <id> --native
  native/target/release/prove-it` for each, on freshly built `dist/`, addon and binary. Any native
  "differs" is a blocker: fix it or decline the run as not native.
