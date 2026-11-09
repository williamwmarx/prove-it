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
