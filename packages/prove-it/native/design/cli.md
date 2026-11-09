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
