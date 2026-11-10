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
`[counterexample |-> CounterExample, vars |-> vars]`. `tla-trace` writes both files; the binary
doesn't call it yet (its arguments, SANY's report of the extra modules, and the postconditions'
order are the binary's).

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
`-lncheck` or `-metadir`, and, on the `tlc2.TLC` form, a second module or none. Each message was
compared with a TLC built from the clone at d8fb231.

It models `-config` (with or without `.cfg`, as TLC), `-continue`, `-deadlock`, `-dump`,
`-fp 0`, `-lncheck`, `-metadir`, `-modelcheck`, `-nowarning`, `-seed`, `-tool`, `-workers` and the
trace-spec switches (`-generateSpecTE [nomonolith]`, `-noGenerateSpecTE`/`-noTE`,
`-noGenerateSpecTEBin`/`-noTEBin`). Every other option TLC reads (`-simulate`, `-difftrace`,
`-coverage`, `-maxSetSize`, `-dfid`, `-fp N`, ...) is not native, as are the shapes where TLC
throws (`-dump` last, an empty argument), an argument that isn't ASCII, and `Spec.cfg` named as
the module on the `tlc2.TLC` form. `-lncheck off` is not native either: TLC then checks no temporal property (`LiveCheck.java:238`).
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

## Handoff

- tla-front feeds the search, or reports where TLC stops before it (above). Parity measures the
  binary that way: `differential --native-only --native <binary>`, gated on
  known-differences.json's `tlc/native` entries.
- Sweep for wrong output after a big push: list the corpus models whose configuration uses
  SYMMETRY, VIEW, ALIAS, POSTCONDITION(S) or `_POSSIBLE`, and run
  `bun scripts/run.ts differential --compare-backends --filter <id> --native
  native/target/release/prove-it` for each, on freshly built `dist/`, addon and binary. Any native
  "differs" is a blocker: fix it or decline the run as not native.
