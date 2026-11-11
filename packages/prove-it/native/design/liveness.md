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

The native binary reports it itself (`ViolationKind::Accepted`). TLC's counts at that state come
from the graph: the initial states plus each expanded state's successors and new states up to it,
and its depth then. TLC adds the states to the behavior graphs as it searches even under
`-lncheck final`, so the engine adds them as TLC would where its search stops anyway:
- Past `MAXIMUM_GRAPH_STATES`, before it hands the graph over: TLC's Github710b, whose x grows
  without bound, stops at its third state, which the binary now reports.
- At a deadlock or an invariant violation, the deadlocked state included, which TLC adds after it
  reports the deadlock. Where no state reaches an accepting node, TLC reports the violation, which
  the binary prints. Where the deadlocked state reaches one (Github710d), TLC reports the deadlock
  and then the node's counterexample, with the deadlock's counts: the deadlock carries the path
  (`AcceptedTrace`), which the binary rebuilds from the same store and prints after the
  deadlock's trace. It hands over where a postcondition would check the traces, and where an
  invariant violation's state reaches one.

Where no tableau node of a model with no PEM conditions accepts every behavior (`hasEmptyPEM`),
TLC can't stop this way and the checker evaluates nothing. It still hands over where TLC would fail
evaluating an atom the engine couldn't answer, a state predicate on any state or ENABLED on an
expanded one, as on InitialLivenessEvaluationError.

## An atom that fails to evaluate (as built)

TLC evaluates the atoms as it adds each state to the behavior graphs, and stops at the first that
fails, reporting it as an error in the next states, with the call stack first
(`Worker#doNextCheckLiveness`): Github607, tla-rs liveness_error. The engine answers an atom it
can't evaluate as UNKNOWN, so the checker records the first unanswered atom it reads as it adds
an expanded state (`Liveness::unanswered`), in TLC's order. The engine reports it as
`ErrorSite::Atom`: the path to the state being added, then the successor or the step's next state
the atom reads, with the counts and out-degrees the graph holds up to that state. The binary
evaluates the atom again with `tla-trace`, and prints TLC's report where it fails as TLC does, or
isn't native where it holds. TLC's call stack records no node for the `<<A>>_v` of `WF_v(A)`,
which the front writes at A, and ENABLED names the fairness condition where A leaves a variable of
v unassigned (2148).

An atom that fails on an initial state stops TLC's `DoInitFunctor` there, and TLC reports it with
the state. TLC then replays the initial states with its `CallStackTool` (`ModelChecker#doInit`),
adding to the behavior graphs only those its first pass didn't find. Where an atom fails again on
one of them, TLC prints that call stack, the initial predicate's frames then the atom's, and exits
as for it. Its counts are the replay's, up to that state, or all the initial states where nothing
fails again. The engine hands this over (`ErrorSite::InitialAtom`, with the atom the replay may
fail at and its state) where every initial state it generated is distinct, so a state's position
is its count, and where it printed the progress TLC did before the failing state. The invariants
and implied inits the replay checks again held of every initial state, as the engine checked them
before it got there. A property `[]P` of a
state predicate P isn't an atom: TLC checks it as an invariant, which the replay checks again on
the states it found, the failing one first.

## A failure of the next-state relation in a model with temporal properties (as built)

The binary declined it (the `tlc-replay` test's two runs and one of `check`'s). TLC goes on after
the failure. Read from `Worker.run` and `Worker#doNextCheckLiveness` at d8fb231, and checked
against TLC built there:

1. `getNextStates` throws at state s. `ModelChecker#doNextFailed` sets the error state and prints
   the error and the trace to s.
2. The worker doesn't stop. With temporal properties it calls `doNextCheckLiveness` on s with the
   successors Next generated before it failed, and adds the stuttering step from s to s.
3. `LiveCheck#addNextState` evaluates, for each solution of the tableau:
   1. `checkAction` on each successor, in the order of the `SetOfStates`, which is the order of
      their fingerprints' hashes, not the order Next generated them in;
   2. `checkState` on s, which holds the ENABLED and state checks;
   3. with a tableau, the consistency of each successor with the tableau's nodes.
4. If one of those fails, TLC evaluates them again with a `CallStackTool` and prints that call
   stack (`EC.TLC_NESTED_EXPRESSION`). It sets `keepCallStack` to false, so TLC doesn't print
   Next's call stack, and its second `doNextFailed` prints nothing, since the error state is
   already set.

So TLC prints Next's error and the trace either way. After them it prints Next's call stack when
every liveness check on s holds, and the first failing check's stack when one fails. In the
`tlc-replay` model, the ENABLED of the failing action's fairness fails on s, so TLC prints the
stack Spec, the fairness condition, Next, the action. A model whose fairness names an action that
doesn't fail (`WF_x(B)` while A fails) prints the plain Next failure.

The engine orders the failure. At a Next failure in a model with temporal properties it adds s to
the graph as an expanded state whose steps are those Next took before it failed (`Graph::partial`;
the steps the search records are the in-model successors, as TLC's `SetOfStates` holds them), so
the tables answer the atoms on those steps, the stuttering step and the successors, and ENABLED
on s is evaluated rather than read from the partial steps. `find_unanswered` then adds the states
up to s in TLC's order, the solutions' action checks on the steps in fingerprint order, then the
state checks, then the tableau's consistency:
- an atom that fails on a state before s is TLC's stop, as before (`ErrorSite::Atom`);
- an atom that fails on s or one of its steps is `ErrorSite::NextAtom`, with the state past s it
  reads, if any. `tla-trace` evaluates Next's failure for the message, the trace and the code, and
  the atom's for the call stack, which the binary prints in place of Next's. TLC exits by the
  error's code, as no replay runs: a failure that isn't an EvalException exits 255, not 75. Where
  the atom's rerun has no call stack (a subscript's comparison), TLC replays Next and prints its
  call stack, and so does the binary;
- where every check on s holds, the search reports Next's failure, which the binary prints as it
  does without temporal properties.

The search reports neither where it can't tell: where an atom the tables leave unanswered holds
when evaluated (one after it may fail), where the search or an atom prints (TLC evaluates the
atoms twice where one fails, and its replay of Next prints again), under SYMMETRY or a VIEW, where
an atom reads TLC's registers or the diameter, where a tableau node of s accepts every behavior,
and for a successor that isn't complete, which TLC reports otherwise. The `tlc-replay` runs are
native. `check`'s still declines, now where `tla-trace` evaluates Next again ("SUBSET of a
non-set"): TLC's Next doesn't fail there, as its `\E` over `{1} \cup SUBSET 3` stops at 1, which
the engine's eager enumeration doesn't; it is the ENABLED of the fairness that fails, and its
rerun with the call stack fails to fingerprint, so TLC replays Next for its call stack.

## A deadlock in a model with temporal properties where a check fails (as built)

The binary declined it ("the engine stopped: deadlock"; the `tlc-replay` test's deadlock runs).
Read from `Worker.run`, `Worker#doNextCheckLiveness`, `ModelChecker#doNextSetErr` and
`ModelChecker#doNextFailed` at d8fb231, and checked against TLC built there:

1. `getNextStates` generates no successor of s. The worker's `doNextSetErr` sets the error state
   with `keepCallStack` false, prints "Deadlock reached." and the trace to s, and checks the
   postconditions on that trace.
2. With temporal properties the worker goes on to `doNextCheckLiveness` on s, whose successors
   are only the stuttering step from s to s, and `LiveCheck#addNextState` runs the checks of the
   section above in the same order: each solution's `checkAction` on the stuttering step, its
   `checkState` on s (ENABLED and the state checks), then the tableau's consistency.
3. Where one throws an EvalException or a TLCRuntimeException, TLC runs them again with a
   `CallStackTool` and prints that call stack where it has one (`EC.TLC_NESTED_EXPRESSION`), then
   rethrows. The worker's `doNextFailed` finds the error state set and prints nothing, and no
   replay runs, as `keepCallStack` is false.
4. Where the rerun throws a FingerprintException instead (a value with a source, as `<<1>>[2]`),
   it isn't caught there, and reaches `doNextFailed` the same way: TLC prints nothing of it.
5. Where a POSTCONDITION is a definition TLC computed as it started, such as `Post == TRUE`,
   `Spec#getPostConditionSpecs` rejects it in step 1, after the trace, with an exception that
   leaves the worker's loop for its catch, which prints nothing as the error state is set. The
   worker never reaches step 2: no check fails on s and no node of s accepts, so TLC prints the
   plain deadlock, and the binary drops what the engine found there.

So TLC prints the deadlock, the trace and what the postconditions print, then the failing check's
call stack, if any, then the statistics, and exits 11 whatever failed. Where every check holds it
prints the plain deadlock. `-tool` prints the stack as message 2103, and `-lncheck final` changes
nothing, as TLC adds each state to the behavior graphs as it searches either way. A check on s
can fail only where it reads s alone: a state predicate of a successor is a check of the state
before it, and a step's subscript is evaluated on both its states, so an action atom fails on the
stuttering step only at a deadlocked initial state.

The engine adds s to the graph as an expanded state with no steps, as it did for an accepting
node (Github710d), and lets `unanswered_at` reach s too. The first atom the tables leave
unanswered on s that fails as TLC fails becomes `ViolationKind::Deadlock::atom` (a
`DeadlockAtom`, `is_extra` for the stuttering step); one that holds when evaluated declines, as
one after it may fail. The binary evaluates it again with `tla-trace` (`Site::DeadlockAtom`) for
the call stack alone, which it prints after the postconditions' report; where `tla-trace` finds
the rerun throws a FingerprintException it prints none. It declines where the atom prints, and,
as before, where the search or an atom prints or the search doesn't follow TLC's checks (SYMMETRY,
a VIEW, the diameter, TLC's registers). A grid of 59 specs (ENABLED of WF and SF, state
predicates, the stuttering step's subscript, several fairness conditions and properties,
invariants, an ALIAS, a postcondition, a constraint, deadlocks at an initial state and later),
each in plain, `-tool`, `-lncheck final` and both, on one thread and four, matched TLC on 424 of
472 runs and declined the other 48: Print in Next or an atom (3 specs), a function applied
outside its domain, whose message `tla-trace` doesn't give, and two atoms that fail on a state
before the deadlock, or with no deadlock check, which TLC words as a FingerprintException, as
before. The engine had printed the plain deadlock where the stuttering step's subscript fails on a
deadlocked initial state, as the tables left that step unanswered and the verdict reads no action
atom; it now prints TLC's call stack there. `prove-it-cli/tests/deadlock-live.rs` holds a
representative set.

## Print at a stop (as built)

Where the search stops, at a deadlock, a violated invariant or action property, or a failure of
Next or of an invariant, in a model with temporal properties whose spec prints, TLC prints in an
order read from `Worker.run`, `Worker#addElement`, `Worker#doNextSetErr`,
`Worker#doNextCheckLiveness`, `LiveCheck#addNextState` and `ModelChecker.modelCheck` at d8fb231:

1. As it searches, each expansion's prints, then those of the atoms as it adds the state to the
   behavior graphs, late nodes included, up to the state s it stops in, and s's expansion up to the
   stop.
2. The error and the trace, with what rebuilding the trace prints (`TLCTrace.printTrace`), and,
   where the worker reports it (`Worker#doNextSetErr`: a deadlock or a violation), the trace
   rebuilt again for the postconditions (`doPostCondition`), whatever the postconditions.
3. The worker goes on: an exception in `getNextStates` is caught (`doNextFailed` prints nothing
   once the error state is set), and `doNextCheckLiveness` adds s with the successors already in
   its `SetOfStates`, the one that violated or failed an invariant among them, since
   `isSeenState` put it there before the invariants were checked, and the stuttering step. So TLC
   adds s after an invariant that fails too, which TLC confirms: seven prints after the trace that
   the model without its property doesn't print.
4. Once the workers are done, where the error keeps its call stack, the replay of s's expansion
   (`ModelChecker.doNext`), which prints Next's prints again, then the call stack.

The engine follows it where the search held its prints (`place_stop_prints`): it adds s to the
graph, with its steps so far marked partial, and the new successor it stopped at as a state past
the stored ones (`Graph::stopped`, the edge `record_step` keeps). `tla_live::added_events` adds the
states with each atom's evaluation logged; the events up to `Event::Expanded(s)` place the prints
before the stop, as `order_printed` does for a complete search, and those after it are carried in
`Violation::added`, which the binary prints after the trace (step 2) and before the replay's
prints (step 4).

A late node of s runs Next from s in full, checking no invariant (`LiveCheck#addNextState`). After
a deadlock that is the expansion the search printed. After a violation or an invariant that fails,
the engine runs Next from s again and follows it where it takes the steps the search took, so the
late node's steps are the graph's. It declines, each with its reason:
- a late node of a state whose next states fail: Next fails again there, and TLC reports that
  failure after evaluating the checks a second time on a graph the first attempt changed
  (TLC's output shows the late node's prints, then fewer prints again, then the call stack);
- a late node of s whose full Next takes other steps than the search took (a second successor,
  or two equal ones), with several actions, or with constraints;
- an atom the engine doesn't answer or a node that accepts every behavior as TLC adds the states,
  as where the fairness action is the one that fails on s (TLC reports the atom's failure, and
  evaluates the checks twice);
- an atom that prints as TLC adds an initial state, as for a complete search;
- SYMMETRY or a VIEW, atoms that read TLC's diameter or level, and a POSTCONDITION where the
  added state prints.

Where the engine declines for any of those reasons and nothing prints past the initial states,
neither the search, nor the atoms, nor Next run again from s in full as a late node of s would, it
reports the stop as where nothing prints, which matched TLC before: a model whose initial predicate
alone prints and whose property reads `TLCGet("level")`, or whose deadlocked state's atoms under
strong fairness the engine doesn't answer, or whose deadlocked state's node accepts every behavior.
`place_stop_prints` leaves the search as it found it when it declines, for that report.

Verified against TLC on 360 generated specs (the stop's kind and depth, prints in the action, in a disjunct, in the fairness action alone or in the property, three
properties, WF, SF or none), each in plain, -tool, -lncheck final and both, on 1 and 4 workers:
2880 runs, 1936 print what TLC prints, 944 decline, none differ.

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

The native binary prints such a lasso itself. The engine hands it the stored states, unlabelled,
and `tla-trace` rebuilds those TLC prints as it does a reduced safety trace, the step back into the
cycle with them: the stored path with the cycle's first state once more, whose last step's action
is the loop's. TLC then names the properties the rebuilt lasso violates
(`Liveness.findViolatedProperties`), which `tla_live::violated_on_lasso` evaluates on it, each atom
by `Rebuilder::answer_atom` on the rebuilt states.

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

## TLCGet("level") in the temporal properties (as built)

TLCGet("level") reads the level of the state TLC evaluates (`TLCGetSet`), which TLC set as it
generated the state: 1 for an initial state, else one past the state it expanded. As TLC adds an
expanded state to the behavior graphs, the state and its stuttering step are at the state's own
level, and each successor is one past it, whatever level the search first found it at. So a step
back to an earlier state reaches it at a level the search never gave it: `<>(TLCGet("level") = 3)`
holds on a cycle of three states the search found at levels 1 and 2.

- The engine answers such a state predicate for each state, and for each state a step reached, by
  the step's edge (`Atom::LevelState`, `Slot::Reached`). It answers an action at its step's levels,
  with the stuttering step's next state at the first state's level (`Atom::LevelAction`).
- The checker keeps no consistency of a state with a tableau node across the steps that reach it,
  as TLC keeps none.
- TLC names the properties a lasso violates from the lasso it rebuilt, each state a successor of
  the one before, so at its position, and the step back into the cycle at the cycle's start. The
  binary names them so (`is_level_read`).
- TLC keeps the first state it puts in a set of successors, so a step from a state to itself leaves
  the stuttering step at the generated successor's level, one past the state's, which the checker
  doesn't tell apart. The engine declines a level atom there, and in ENABLED, in a subscript, under
  SYMMETRY or a VIEW, and where atoms print or read the diameter.
- `lasso-grid/Level*` holds 40 specs for which the binary prints what TLC built at d8fb231 prints.

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

Where it checks this way, the search keeps its graph however large it grows. Past 4 million states
(`MAXIMUM_GRAPH_STATES`) the engine still hands the graph over where it doesn't check this way, or
where a check part way through couldn't decide, say on an atom the engine doesn't answer: the
interpreter checks as the graph grows, and even under `-lncheck final` TLC stops at the first state
whose tableau node accepts every behavior (TLC's Github710b, whose x grows without bound, stops at
its third state), which the engine finds only once the search is done. TokenRing at N = 8, M = 7
(5.8 million states, 41 million steps) checks natively in 91 s at 2.6 GB peak on 4 cores, where the
interpreter took 135 s and 9.1 GB on Depot's 16 and TLC 149 s and 2.75 GB; 49 s of it answers
WF_vars(Next)'s action on each step, as TLC does. Under `-lncheck final` the engine hands it over.

With PROVE_IT_WORKERS above one, `answer_atoms` answers the state and action atoms on that many
threads, each a run of the states over the search's store, as a parallel search's threads expand a
level: an evaluation that neither prints, draws nor reads TLC's diameter is the same on any thread.
Each extra thread's overlay copies the store's values, as the search's do, so each costs about the
store's size in memory. TokenRing at N = 8, its graph kept, checks on 4 threads in 51 s rather than
81 s, its atoms in about 19 s rather than 49, at 5.0 GB peak rather than 2.6. Sharing the store
instead slows a search on one thread by 9 to 18 %, so the parallel atoms stay opt-in: the engine
answers them on one thread unless PROVE_IT_WORKERS asks for more.

## Speed against TLC (measured)

`scripts/bench-liveness.json` lists the liveness models: the 13 corpus models with temporal
properties that both checkers finish in seconds, and the scaled models in `benchmarks/liveness`,
which TLC takes a minute or more to check. The Benchmark workflow runs them with
`suite = bench-liveness.json`, and the scaled models on `runner = depot-ubuntu-24.04-16`.

Depot run rghnhzfvg3 (16 cores, 3 runs, `--checkers tlc,prove-it-rust`, Prove It at 48ef0dd), median
wall seconds and peak resident memory. Rust agreed with TLC on all 16 models and is 11.5x faster
in wall time (geometric mean).

| Model | Distinct states | TLC | Rust |
| --- | ---: | ---: | ---: |
| StarkMutex (pcal) | 23,168 | 2.64 s, 1214 MB | 0.18 s, 105 MB |
| TokenRing (ewd426) | 46,656 | 1.15 s, 651 MB | 0.18 s, 95 MB |
| nbacg_guer01 | 24,922 | 2.04 s, 1207 MB | 0.12 s, 83 MB |
| MCDisruptor_SPMC | 8,496 | 0.88 s, 625 MB | 0.10 s, 86 MB |
| MacroQuicksort (pcal) | 31,092 | 5.50 s, 1489 MB | 0.12 s, 87 MB |
| ReadersWriters | 21,527 | 1.40 s, 724 MB | 0.11 s, 83 MB |
| cf1s_folklore | 10,016 | 1.34 s, 471 MB | 0.09 s, 81 MB |
| SingleLaneBridge | 3,605 | 2.81 s, 1190 MB | 0.10 s, 85 MB |
| FastMutexWithGoto2 (pcal) | 15,900 | 0.83 s, 484 MB | 0.07 s, 80 MB |
| Dijkstra1 (pcal) | 5,510 | 0.60 s, 354 MB | 0.05 s, 75 MB |
| Euclid (pcal) | 6,352 | 0.49 s, 236 MB | 0.04 s, 75 MB |
| Barriers | 29,279 | 2.07 s, 1258 MB | 0.33 s, 136 MB |
| bcastByz | 14,424 | 8.23 s, 1582 MB | 0.39 s, 153 MB |
| StarkMutex, N = 4 | 399,763 | 75.0 s, 1987 MB | 4.73 s, 654 MB |
| Barriers, N = 8 | 536,319 | 44.5 s, 1701 MB | 6.18 s, 508 MB |
| TokenRing, N = 8, M = 7 | 5,764,801 | 149 s, 2750 MB | 135 s, 9098 MB (interpreter) |

The scaled models check in time and memory proportional to their states, but for TokenRing at N = 8.
There the engine handed over at the start, and the interpreter checked the model. The initial
predicate draws from a set of 5.8 million functions, past the 1e6 bound the engine had copied from
the TypeScript engine, and past 4 million states (`MAXIMUM_GRAPH_STATES`) the engine hands its graph
over anyway, so that the interpreter checks the properties as the graph grows, as TLC does. The
suite now scales TokenRing to N = 7, M = 8 (2.1 million states) instead, which the engine checks
itself with its bound on enumerated sets at 2^24. bcastByz at N = 5 (1.07 million states) is out of
the suite: TLC didn't finish it in 1500 s, and Rust took 284 s, nearly all of it on one action atom,
Receive's `\E` over `SUBSET sent`, evaluated on each of 38 million steps.

## Atoms that use TLC's registers (as built)

TLC evaluates the atoms as it adds each state it expanded to the behavior graphs
(`Worker#doNextCheckLiveness`), between the expansions, so an atom that sets or reads a register
(TLCSet, TLCGet of a number or a name) and a next-state relation that does see each other's
effects in that order: TLC's Test2 counts 20 evaluations of Next over 5 states, one in the search
and three in WF's ENABLED and action for each. Answering the atoms in tables once the search is
over can't give that, so the native checker answers them as the search goes:

- `tla-live`'s checker no longer borrows the graph and the tables: each call takes a `Source`, the
  graph so far and the atoms' `Answers`. `Answers::answer(atom, slot, diameter)` is asked each
  time the checker reads an atom, at a `Slot` (a state, a step from a state by its edge, or a
  state's stuttering step); `Tables` is its implementation for a search that is over, with the
  position of an answer in an atom's table, which the logged events and `Unanswered` still name.
- `tla_live::Online` is the checker driven state by state, with the effects on, so it asks each
  atom each time TLC evaluates it: `add_initial_state`, `add_state` once the search expanded a
  state, `take_events`, `finish` for TLC's check of the graphs at the end.
- `tla-engine`'s `LiveAnswers` evaluates an atom when asked, on the machine as it is then:
  `<<A>>_v` as TLC's `LNAction#eval` does, v of each state and A only where they differ.
- The search runs this way where it reports violations itself (the native binary) and an atom
  uses the registers (`EngineContext::is_live_registered`): after each expansion it adds the
  state (`add_online`), and what the search and the atoms print comes out as it is printed, with
  nothing held. It makes no check part way through the search.

Verified against TLC d8fb231 on models whose registers are a running hash of every evaluation
(branching steps, two initial states, WF and SF, an atom that prints): the registers a
POSTCONDITION prints are TLC's.

It declines, each with its reason, where it doesn't follow TLC: under SYMMETRY or a VIEW; with an
atom that reads TLCGet("diameter"); where TLC evaluates an atom as it finds an initial state (a
tableau whose initial nodes have state predicates, `Online::asks_initial_states`), which would
come between the initial predicate's own evaluations; where TLC runs Next again for a late node
(`Event::Late`); at a node that accepts every behavior; at a counterexample, whose states TLC
rebuilds, with what Next sets, before it evaluates the properties on it; at a deadlock, whose
state TLC adds after it reports it; and where an atom doesn't evaluate. The interpreter and the
TypeScript engine's path are as before: there such an atom is one the engine doesn't answer.

## Handoff (liveness session, 2026-11-09)

Done on native-parity:
- A deadlocked state that also violates a temporal property: the deadlock, then the property's
  counterexample (Github710d).
- A property an initial state violates (2108, DoInitFunctorProperty). The IR carries each
  initial predicate's name.
- An atom that fails as TLC adds a state to the behavior graphs (Github607, tla-rs
  liveness_error): `Liveness::unanswered`, `ErrorSite::Atom`, `Site::Atom`. ENABLED names the
  fairness condition whose action leaves a variable unassigned (2148).
- Optional Next (tm/AS): `EngineContext.next` is an `Option<Step>`. With initial states and no
  next-state relation the search stops with `ViolationKind::NoNextState`, which the binary
  prints as 2115 with no statistics, exit 75; with no initial states it completes. It declines
  with temporal properties, a POSTCONDITION or `_POSSIBLE`, which TLC never reaches there.
- Scoped properties (tm/Github1161): `Conjunct::Scoped`, checked whole, and
  `Compiler::compile_scoped` for the invariants, action properties and implied inits of an
  instance; tla-trace's `check_violation` reads each in `scope_context(scope)`, and
  `evaluate_failure` declines an implied init in a scope that fails to evaluate.
- A lasso whose atoms print (UserModuleOverrideAnnotation): TLC evaluates each property on the
  lasso it rebuilt (`Liveness.findViolatedProperties`), each atom anew. `tla-live` logs those
  evaluations after `Event::Lasso`, the engine carries what they printed in
  `ViolationKind::Lasso::printed`, and the binary prints it before the violation.
- An atom that fails as TLC adds an initial state (InitialLivenessEvaluationError): TLC adds
  each initial state to the behavior graphs before it checks it or reports the initial states
  (`DoInitFunctor`), so the search asks `tla_live::find_unanswered` of the initial states before
  it reports them, and stops with `ErrorSite::InitialAtom`. TLC then replays the initial states,
  which the engine follows only where there is one; with more it declines. A violation found
  among the initial states is reported only where every atom evaluates on them
  (`answers_initial_atoms`). At a safety stop, the first atom unanswered on a state TLC had
  added by then (`unanswered_at`) is reported as at the search's end, but only where evaluating
  it fails as TLC fails (`atom_failure`): the tables of a search that stopped also leave
  unanswered what the checker asks of states not yet expanded, which TLC evaluates without
  failing, and there the violation the search found stands (ACP_NB_WRONG_TLC, SDP_Attack_Spec).
- A lasso a check part way through the search finds: the search builds the violation with
  `to_lasso` and the counts so far, and the binary prints it after the check's start, which the
  search reported as the check began.
- Test2: atoms that use TLC's registers are answered as the search goes (the section above).
- YoYoAllGraphs: without the community modules' Java overrides TLC fails computing the initial
  states, quantifying over Seq(S). A quantifier fails at the first bound TLC only tests for
  membership (`INFINITE_BOUND`, as `Tool.contexts` takes every bound's enumerator first);
  `tla-trace` follows a filter TLC kept lazy into the comparison that enumerates it
  (`follow_lazy_filter`); the binary reports a failure among the initial states of a model with
  temporal properties, which the search hands over only where the atoms of the initial states
  evaluate; and the call stack's first frame is the list a definition wrote, as both front ends
  keep a definition that is a state predicate whole as one of the specification's initial
  predicates (`gaps.md`, "The specification's initial predicates, as TLC keeps them").
- TraceMultiNodeReads: without the Java overrides its CONSTRAINT chooses from
  [STRING -> STRING] on the first initial state. Enumerating a set of functions whose domain
  TLC can't enumerate is one of TLC's failures (`INFINITE_DOMAIN`); `tla-trace` marks a failed
  enumeration by CHOOSE as one in a value's method, and for a constraint of an initial state
  gives TLC's report: the error with the state, then the FingerprintException of TLC's replay
  of the initial states, with the initial predicate's frames and the constraint's
  (`Site::InitialConstraint`); the binary reports a failure among the initial states whatever
  the ALIAS and the postconditions, which TLC doesn't reach there. Where an atom uses the
  registers and TLC would evaluate it of an initial state, the search now declines only once
  it has an initial state to add, so a failure before the first one is reported.

Declined after the pre-PR review (infinite-sets session, 2026-11-10), each with a test in
`prove-it-cli/tests/cli.rs`:
- A stop, a deadlock or an invariant, in a model with behavior graphs where an expansion
  printed: TLC runs Next again from a state it adds a tableau node of late, printing again what
  Next prints, which the search doesn't place before its stop. Now placed: see "Print at a stop".
- A late node's prints where Next has several actions: TLC runs it action by action there, with
  the atoms of each action's successors between (`LiveCheck.addNextState`); `order_printed`
  places them only where Next is one action.
- A lasso whose last state is its cycle's first and which isn't the stuttering shape: TLC ends
  it "State N+1: Stuttering" (`LiveWorker.printTrace`), which the binary doesn't follow.
- Fixed with them: an atom that fails adding a state exits by the error's own status (255, 14
  for an assertion, 151 for an undefined identifier), one that fails on the initial state is
  followed by the statistics, and the brackets of `<<A>>_v` have no frame.
The TypeScript checker differs from TLC on the second and third alone: see `gaps.md`.

Open, with what is known:
- The front names a property an instance exports by the definition's own name (`Safe`) where
  TLC names it as the configuration's property refers to it (`A!Safe`, `opNode.getName()` in
  `SpecProcessor#processConfigProps`), in both front ends, scoped or not. No corpus model
  reports such an invariant violated. Reported to the coordinator for the front's owner.
- MCEWD687a (both copies) is the infinite-sets session's: see `gaps.md`. The scoped properties
  it needed are in; what is left is TLC's failure enumerating the filter of Seq(S), the
  property invariant's failure site and its replay.
- Where the atoms use TLC's registers, the cases the search declines (the section above): the
  next would be an atom TLC evaluates on an initial state, which needs the checker called from
  `visit_initial` with the machine's state kept around the atom, and a late node, where Next's
  walk from the state runs again for what it sets.
