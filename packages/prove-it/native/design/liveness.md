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
- A successor set dedups entries by the real state, not by index, and keeps the order by
  fingerprint, the key's. Late expansion runs Next from the real successor, which the search may
  never have expanded (it expanded the stored state with the same fingerprint), so the engine
  expands those real states too, after the search, for the late nodes that need them.
- The violated properties come from the rebuilt trace, which the CLI's trace printer builds; Rust
  returns the lasso as indices and leaves `violated` empty there.
- The interpreter, today's oracle, canonicalizes a successor before its liveness checks see it
  (`isCanonicalizedFirst` in `check.ts`), which is not what TLC does. Where it and TLC differ on
  the corpus, TLC's recordings decide, and the interpreter is fixed to match.

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

The scaled models check in time and memory proportional to their states, but for TokenRing at
N = 8. There the engine handed over at the start, and the interpreter checked the model. The
initial predicate draws from a set of 5.8 million functions, past the 1e6 bound the engine had
copied from the TypeScript engine, and past 4 million states (`MAXIMUM_GRAPH_STATES`) the engine
hands its graph over anyway, so that the interpreter checks the properties as the graph grows, as
TLC does. bcastByz at N = 5 (1.07 million states) is out of the suite: TLC didn't finish it in
1500 s, and Rust took 284 s, nearly all of it on one action atom, Receive's `\E` over
`SUBSET sent`, evaluated on each of 38 million steps.
