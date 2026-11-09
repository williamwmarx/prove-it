# Liveness in Rust (stage 3)

The liveness workstream's notes, as built and as planned; DESIGN.md 5.1 and 12.1 set out the
plan and the first part as built.

## Liveness under SYMMETRY and VIEW: what TLC does

Thirty corpus models check temporal properties under SYMMETRY or a VIEW, and `check.ts` leaves
them all to the interpreter ("liveness under symmetry or a view"). From TLC's source (`Worker`,
`SetOfStates`, `LiveCheck`, `LiveWorker`, `Liveness` on tlaplus/tlaplus master, November 2026):
- **Nothing is canonicalized.** Under SYMMETRY, `TLCStateMut#fingerPrint` is the smallest
  fingerprint over the permutations and under a VIEW the fingerprint of the view, but the state
  itself is never replaced: the queue holds the successor as first generated
  (`Worker#addElement`), so a state's own checks (`OrderOfSolution#checkState`) run on that state.
- **The checks see each step's real successor.** `Worker#isSeenState` puts each in-model
  successor in the `SetOfStates` with its fingerprint, and the set keeps two successors with the
  same fingerprint apart unless they are `equals` (`put0`). `LiveCheck#addNextState` evaluates the
  action checks on `(s0, s1)` and the tableau's consistency on `s1` for every entry, before it
  reduces each to its fingerprint: the behavior graph's nodes are `(fingerprint, tableau node)`,
  and an edge is added once, by the first entry that reaches it (`transExists`).
- **Late nodes** (`addNextState` for a node whose state is done) run Next again from the real
  successor `s1`.
- **The counterexample** is a path of fingerprints. `LiveWorker#printTrace` rebuilds real states
  from them, `Tool#getState(fp, previous)` taking the first successor of the previous state with
  that fingerprint, and `Liveness#findViolatedProperties` names the properties from those rebuilt
  states, not from the graph's.

What follows for the engine and `tla-live`:
- The graph's nodes stay the engine's states, by index, but each step needs the successor the
  search actually generated where it differs from the stored one (always possible under a VIEW,
  and under SYMMETRY whenever the stored state isn't that very successor). The engine records
  that successor's ids per step, only under SYMMETRY or a VIEW, and answers the state atoms on
  it as well as on each stored state; an action atom's step is `(stored s0, real s1)`.
- A successor set dedups entries by index and real state, as `put0` does, and keeps the order by
  fingerprint, the key's. Late expansion runs Next from the real successor, which the search may
  never have expanded (it expanded the stored state with the same fingerprint), so the engine
  expands those real states too, after the search, for the late nodes that need them.
- The violated properties come from the rebuilt trace, which the CLI's trace printer builds; Rust
  returns the lasso as indices and leaves `violated` empty there.
- The interpreter, today's oracle, already does what TLC does. `canonicalizeState` in `check.ts`
  only shares equal values between states; it picks no representative. The interpreter stores
  each successor as first generated, tells states apart by the representative's fingerprint
  (`getFingerprintState`), and gives its liveness checker each step's real successor (`state:
  isStored ? stored : successor.state` in `visitSuccessor`), and late expansion runs Next from
  that real state. Measured on main at 148cdae, with the engine handing over its keys (the
  representatives) in place of the stored states: the interpreter's checker then finds other
  lassos on OneBitMutexMC and NQ/MC, because the engine's representative of a state is not the
  state the interpreter stored. So the native checker must see what TLC sees: the stored state
  for a state's own checks and the real successor for each step.

## Labels of a lasso's steps (as built)

After a lasso, the engine finds the action of each of its steps as TLC's `Tool#getState` does:
from each state, the first of TLC's actions (`Model.actions`, compiled whether or not the search
walks them) with a step to the next state of the lasso, and from the last state to the cycle's
first. `SearchOutcome::Complete::lasso_actions` holds their positions, `None` for the stuttering
step of a lasso whose cycle is its last state, and is empty when the engine has no walk of TLC's
actions. Under `PROVE_IT_LIVE_CHECK=1` the interpreter compares their labels with the trace's: no
difference on the 30 corpus lassos.

## An accepting tableau node (as built)

Where the native checker finds a tableau node that accepts every behavior (`Verdict::Accepted`),
TLC reports the violation as it adds the state to the behavior graph, with the counts the search
had then. The interpreter replays the engine's graph for those counts only, without its own
liveness checker, and at that state reports the native checker's path: Github1389Counting, the
one corpus model this reaches.

## Temporal formulas inside a predicate (as built)

A liveness atom can be an operator whose body holds a temporal formula in a branch the run never
takes, such as TLC's Github1389ViolatedB/C, where the atom is `Reach(0)` of a recursive `Reach`
whose other branch is `<>(Reach(n - 1))`. The engine compiled none of it; it now compiles `[]`,
`<>`, `WF` and `SF` to a stop at run time ("a temporal formula in a state"), so the native checker
decides both models, and where a run does reach one the interpreter reports the error as TLC does.

## Liveness under SYMMETRY and VIEW (as built)

Under SYMMETRY or a VIEW the search records the successor each step generated, and
`graph_tables` answers the atoms on the stored states and then on each successor a step reached
that differs from the state stored for its fingerprint, once. `tla-live` takes those positions as
`Graph::reals`: a state's own checks and the tableau's consistency read the real successor, an
action atom the step `(stored s0, real s1)`, and a successor set dedups on the stored index and the
real state.

A late node of a state the search reached but didn't store has TLC run Next from that state
(`TableauLiveChecker#addNextState`), which the search never did: it expanded the stored state with
the same fingerprint. `tla-live` then returns `Verdict::Unexpanded`, and the engine takes the
steps from each such state it hasn't yet (`expand_reals`), as TLC does: each successor through
each of TLC's actions when the search labels its steps, in the model and with the action
constraints, with the stored state with its fingerprint. The engine answers the atoms again and
checks again, until the checker asks for no state it hasn't expanded. The state checks of a late
node are of the state it reached, as TLC sets them on the node (`node_reals`).

The checker names no violated property there: TLC names them from the trace it rebuilds, which the
interpreter's printer rebuilds as TLC does. The labels of a lasso's steps come from that rebuilt
trace too: from each rebuilt state, the first successor of TLC's actions with the fingerprint of
the next state of the lasso, as `Tool#getState` takes it.

A replay of the graph would hand the interpreter's checker the stored states, so when the native
checker declines, or under `PROVE_IT_LIVE_CHECK=1`, the interpreter searches again from the start.
On the 26 corpus models with temporal properties under SYMMETRY or a VIEW, all 26 are decided
natively (23 lassos, 3 hold); their outputs match TLC's recordings, and under
`PROVE_IT_LIVE_CHECK=1` the verdicts, lassos, branches and labels match the interpreter's.

## Print while checking the temporal properties (as built)

TLC prints what Print and PrintT print each time it evaluates them, and its liveness checker
evaluates as it adds each state to the behavior graphs, right after the search expands the state:
ENABLED of the fairness runs Next, and so does each action check on each step. The interpreter's
checker, with nothing shared where the spec has repeated effects, evaluates as often as TLC, which
is how it matches TLC's output on Euclid3 and ULEvenOdd, whose Next prints four times per state.

The native engine evaluates every atom on every state and step before the check, so the order
comes from the checker instead:
- With temporal properties and a spec that may print, the search holds what it prints, the initial
  states' and each expansion's, and the count of initial states, rather than reporting them.
- `answer_atoms` keeps what each evaluation of an atom printed, by its position in the table, runs
  ENABLED on each state rather than answering it from the steps, and evaluates an action on every
  step.
- `tla-live`, told the atoms have effects, keeps no result across evaluations, as the interpreter's
  checker does then (no shared rows, no consistency kept, `evaluateLive`'s cache within one check),
  and logs each atom it evaluates after the state it starts to add (`Event`).
- The engine then reports, in order: the initial states' prints, the count of initial states, and
  for each state its expansion's prints followed by those of the atoms the checker evaluated as it
  added the state, up to the state whose accepting node ends TLC's search. Where TLC runs Next
  again for a late node of a stored state, the engine repeats that state's expansion prints.

Where an invariant may print, or anything reads `TLCGet("distinct")`, that repeat would differ from
TLC's: TLC checks no invariant for a late node, and the count of distinct states has grown since.
So where a late node would repeat prints there, the engine hands over as below.

Where the check isn't decided natively, under `PROVE_IT_LIVE_CHECK=1`, where an atom prints as TLC
adds an initial state, or where the steps from a state the search didn't store print, the engine
hands over with no checkpoint and nothing printed, and the interpreter checks from the start.

## TLCGet("diameter") in the temporal properties (as built)

TLC's `TLCGet("diameter")` is `ModelChecker#getProgress`, `TLCTrace#getLevelForReporting`: the
deepest level of the states the search has written so far, which only grows. The liveness checker
reads it as it adds each state: 1 as it adds an initial state, and as it adds an expanded state the
depth the search reached once it expanded the state. So an atom that reads it has an answer per
state and diameter, not per state.

- The compiler gives the diameter a slot, and the engine declines a model whose search reads it
  (`TLCGet("diameter") in the search`), whose value grows within an expansion.
- The search keeps its depth after each expansion (`Graph::diameters`).
- `answer_atoms` answers an atom that reads the diameter once for each diameter from 1 to the last,
  the tables one after another, and leaves it to the interpreter in a checkpoint.
- `tla-live` (`Graph::diameters`) sets the diameter as it adds each state and once the search is
  done, and reads such an atom's answer for the diameter then.

UserModuleOverride and its Annotation variant, whose property prints and reads the diameter, are
checked natively and match TLC.

## Checks part way through the search (as built)

TLC checks the temporal properties as the search goes too (`ModelChecker#doPeriodicWork`): about
three seconds in and then after each progress report, where the behavior graph grew by more than a
tenth since the last check (`livenessThreshold`) and the checks took less than a fifth of the time
(`livenessRatio`), unless `-lncheck final`. It checks the whole graph each time, but the search for
a cycle passes by the nodes of states not yet expanded (`LiveWorker#checkSccs`), and on a
counterexample it stops at once with the counts so far, states left on the queue and all.

The engine does the same at its progress points: `tla-live` checks the graph of the states expanded
so far, its successors' nodes undone, which is the graph TLC built in the same order. The engine
reports the check's start and end, as the interpreter does, and where it finds a lasso the search
stops and the interpreter prints it with the search's counts and queue. It checks this way where the
checker takes the graph so far as TLC does: not under SYMMETRY or a VIEW, where anything prints,
under `PROVE_IT_LIVE_CHECK=1`, or where an atom reads TLC's diameter. Whatever a check leaves
undecided, the check of the complete graph decides. `PROVE_IT_TEST_LIVE_CHECK_AT=n` makes the first
check after `n` states for the engine and the interpreter alike, for the tests, since the time a
check happens at isn't deterministic.
