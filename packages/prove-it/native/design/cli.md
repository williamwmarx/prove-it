# The native binary, as built

Notes on `prove-it-cli` as it is built, after `native/DESIGN.md` §13.7, which has the first
ones. The plan stays in §13.

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

## The startup phase (planned, DESIGN 14.3)

Today the IR holds values that the TypeScript environment computes by evaluating TLA+ before the
search. To lower IR without an evaluator, the front end leaves them out, and the engine computes
them in a startup phase that runs on the IR before the search. The front-end session (F8) agreed
the boundary: `tla-front` evaluates nothing and returns `NotYet` for a model that needs any of
the items below until this lands. The IR version bump and the matching `ir.ts` change land in one
PR, and `tla-front` then writes the same fields.

What moves, where TypeScript does it today, and what the IR carries instead:

| Item | TypeScript today | IR instead | Engine reports |
| --- | --- | --- | --- |
| Startup values | `evaluateStartupDefinitions` (`evaluate.ts`) over `specification.startupDefinitions`, from `reportStartup` (`search.ts`); each definition node carries the value, or `NO_STARTUP_VALUE` | `startup_definitions: Vec<Index>`, the definitions in that list's order, already filtered as the TS filter does where the filter is static (parameters, a constant or substitution replacing it, constant level); no value in the definition node | each `Print` in order; an error is swallowed, as TLC does, and the definition is evaluated where it's used |
| Substitute checks | `getEvaluationError` (`environment.ts`, after the level analyzer): a substitute TLC evaluates at startup, rejected only when that fails and its level bound is above constant | the substitutes to check, each its definition and its level bound | the error TLC reports |
| Assumptions | `findAssumptionViolation` (`search.ts`), called from `check.ts` after `reportStartup` | `assumptions: Vec<(NodeId, TextId)>` in module order with each one's name | 2104 (false), 2105 (failed to evaluate), with the exit codes |
| SYMMETRY | `getSymmetryGroup` (`symmetry.ts`) evaluates the definition to a set of permutations | the SYMMETRY definition's name (a `ConfigName`), in place of the permutations | the configuration errors `getSymmetryGroup` throws, word for word |
| TLC's actions | `getNextActions` (`spec-description.ts`) splits Next, enumerating the constant sets of its `\E`; `getActionLabel` names each | nothing beyond Next and the IR's version: the engine splits Next itself | the actions and labels, as `Model.actions` holds them now |

Two consequences:
- Once the engine splits Next, the effect guard on TLC's actions (#72: none when evaluating them
  has an effect) goes away, since the engine captures what it prints. That unblocks native traces
  for specs that print (etest3, etest8).
- A configuration constant with arguments (`createOperatorTable` in `environment.ts`) needs no
  evaluation: its rows are the configuration's literals (`toValue`). So the front end writes the
  table itself, in a section `operator_tables` of the values: per builtin, its rows of arguments
  and value in `transfer.ts`'s encoding. The engine formats the table and the arguments with TLC's
  printer for the two errors it raises, so no formatted text is carried.

Agreed with the front-end session in review:
- Substitute checks need no level analyzer on either side. The IR lists every substitute of a
  declared constant by a 0-ary operator definition, with the `dependencies.ts` facts' NONCONSTANT
  bit as its level bound. The engine evaluates each at startup and reports a failure only where
  the bound is above constant. The front-end differential checks that the bit agrees with the
  level analyzer (2,711 configurations, no mismatch so far).
- Action labels read `specification.instanceActions`: the name and location of an instance an
  action was copied through. The IR carries, per definition key an instance copied, the instance's
  name and location. `tla-front` fills it from linking.
- Scope bindings: an IR scope holds a `Value` binding only from the action split
  (`getActions` evaluating an action's constant arguments, `spec-description.ts`), which moves to
  the engine. `Model.scope`, from SPECIFICATION resolved through an instance, holds thunks and
  closures over the AST, which the front end writes without evaluating.

Open before the layout is final:
- Startup definitions whose level depends on a substitution: is the TS level filter static
  everywhere, or does it read values?
- The order TLC reports these in. Substitute checks run while the environment is built, so they
  come first. Then come the startup values, before the constant-level invariant warnings
  (`reportStartup`), and then the assumptions. That still needs checking against TLC's `Tool` and
  `ModelChecker` startup.
- `getActionLabel` depends on the TLC version (1.7.4 or later); the IR already carries the version.

The front-end session reviewed this layout (points above). The IR fields' exact order is fixed in
the implementing PR, with the front end's review.

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
