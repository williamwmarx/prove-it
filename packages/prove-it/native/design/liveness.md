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
real state. A late node of a real state the search didn't store declines ("a late node of a state
the search didn't store"), so expanding those states is the next step.

The checker names no violated property there: TLC names them from the trace it rebuilds, which the
interpreter's printer rebuilds as TLC does. The labels of a lasso's steps come from that rebuilt
trace too: from each rebuilt state, the first successor of TLC's actions with the fingerprint of
the next state of the lasso, as `Tool#getState` takes it.

A replay of the graph would hand the interpreter's checker the stored states, so when the native
checker declines, or under `PROVE_IT_LIVE_CHECK=1`, the interpreter searches again from the start.
On the 26 corpus models with temporal properties under SYMMETRY or a VIEW, 20 are decided natively
and 6 decline on a late node; the outputs of all 26 match TLC's recordings, and under
`PROVE_IT_LIVE_CHECK=1` the verdicts, lassos, branches and labels match the interpreter's.
