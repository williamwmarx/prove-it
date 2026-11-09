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
  added by then (`unanswered_at`) is reported as at the search's end.
- A lasso a check part way through the search finds: the search builds the violation with
  `to_lasso` and the counts so far, and the binary prints it after the check's start, which the
  search reported as the check began.
- Test2: atoms that use TLC's registers are answered as the search goes (the section above).

Open, with what is known:
- The front names a property an instance exports by the definition's own name (`Safe`) where
  TLC names it as the configuration's property refers to it (`A!Safe`, `opNode.getName()` in
  `SpecProcessor#processConfigProps`), in both front ends, scoped or not. No corpus model
  reports such an invariant violated. Reported to the coordinator for the front's owner.
- YoYoAllGraphs isn't a liveness gap: without the community modules' Java overrides TLC fails
  computing the initial states ("TLC encountered the non-enumerable quantifier bound Seq({1})",
  with the call stack). It needs the engine to report "enumerated Seq(S)" at a quantifier's bound
  as TLC's failure, `tla-trace` to give that message, and `print_failure` to take a failure
  computing the initial states of a model with temporal properties. Handed to the coordinator.
- MCEWD687a gets past the scoped properties and stops on "enumerated a filter of an infinite
  set": the infinite-sets session's.
- Where the atoms use TLC's registers, the cases the search declines (the section above): the
  next would be an atom TLC evaluates on an initial state, which needs the checker called from
  `visit_initial` with the machine's state kept around the atom, and a late node, where Next's
  walk from the state runs again for what it sets.
- A POSTCONDITION that reads a register Next sets, after an invariant is violated, prints another
  value than TLC's (TLC 9, the binary 6, for Next == x' = (x + 1) % 4 /\ TLCSet(2, TLCGet(2) + 1),
  Inv == x < 3): TLC's rebuilds of the trace run Next again. No temporal property is involved;
  reported to the coordinator for the trace's owner.
