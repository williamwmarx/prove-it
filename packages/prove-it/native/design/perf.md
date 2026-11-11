# Performance: baseline, profiles and plan

The native binary's speed work after #164, kept here so that every later change is measured the
same way. [speed.md](speed.md) records the closure-level work before it and
[parallel.md](parallel.md) the level-synchronous search. The guard is unchanged: output
byte-identical to TLC on every differential run, and nothing that matches today may become a
decline.

## The suite

`scripts/perf-suite.json` holds fifteen models, chosen to span the engine's workloads and to run
for seconds on the 4-core cloud container:

| Model | Workload |
|---|---|
| MCExactInitialSync | safety, 9.6M cheap states: fingerprints, the state table, the walker |
| PaxosCommit | safety, 17M successors of records and sets: memo tables, guards |
| MCMultiNode (CCF) | safety, 1.5M states of sequences of records: memo tables |
| MCLamportMutex | safety, nested functions and message bags |
| MCbtree | safety, records and sequences: fingerprints, recursion |
| Detlefs | PlusCal with SYMMETRY: canonicalization |
| FastPaxos | SYMMETRY over sets of message records |
| TLCSailfish1 | value-heavy: membership in large sets of records |
| MCabs (CCF) | value-heavy: 349 states of large logs, interning |
| GameOfLife | value-heavy: a function over a grid |
| BufferedRandomAccessFile | value-heavy: sequences, builtins |
| StarkMutex, N = 4 (`benchmarks/liveness`) | liveness under fairness: the liveness checker |
| cf1s_folklore | liveness over 2M states: answering atoms |
| SpanTreeRandom (TLC's test model) | a liveness violation: the lasso and its trace |
| 2PCwithBTM | start-up: checks in milliseconds |

`scripts/bench-suite.ts` runs it. `native` is the native binary on one worker, `native-auto` on
every core, and `native-base` another build (`PROVE_IT_BASE_NATIVE`) on one worker.
`PROVE_IT_NATIVE` names the binary, by default `native/target/release/prove-it`. TLC and the
binary both run with the differential's options without its seed: `-nowarning -fp 0 -lncheck final
-noGenerateSpecTE`.

```sh
cd packages/prove-it
(cd native && cargo build --release --locked -p prove-it-cli)
bun scripts/fetch-corpora.ts
# A change against main: build main's binary elsewhere, then
PROVE_IT_BASE_NATIVE=/path/to/main/prove-it \
  bun scripts/bench-suite.ts --suite perf-suite.json --checkers native,native-base --runs 5
# With TLC as the reference
TLA2TOOLS_JAR=/path/to/tla2tools.jar \
  bun scripts/bench-suite.ts --suite perf-suite.json --checkers native,native-auto,tlc,tlc-auto
```

The script times processes, so it runs under Bun rather than through `scripts/run.ts`: Node's V8
buys nothing there. Each run is a fresh process, the checkers take turns in each round, and the
JSON keeps every run.

## Baseline

`main` at 232aa8d, on the 4-core cloud container (Intel Xeon at 2.30 GHz, 16 GB). Median wall
seconds of 5 interleaved runs, with the min–max range. RSS is the median peak. The binary
searches on one thread whatever `-workers` says (`Settings.threads` is 1). The 4-thread column is
an experimental build that sets `threads` from `-workers`: medians of 3 runs, the same machine.

| Model | Distinct | 1 worker, s | States/s | RSS MB | 4 threads, s | Speedup | RSS MB |
|---|---:|---|---:|---:|---:|---:|---:|
| MCExactInitialSync | 9,610,407 | 17.24 (17.17–17.66) | 557k | 1,093 | 9.45 | 1.85× | 1,327 |
| PaxosCommit | 1,321,761 | 27.23 (26.74–27.84) | 49k | 744 | 10.23 | 2.61× | 2,127 |
| MCMultiNode | 1,546,226 | 7.79 (7.73–7.85) | 198k | 542 | 3.30 | 2.35× | 1,121 |
| MCLamportMutex | 724,274 | 3.08 (3.00–3.24) | 235k | 143 | 1.37 | 1.91× | 195 |
| MCbtree | 374,727 | 0.90 (0.85–0.93) | 416k | 50 | 0.44 | 2.04× | 73 |
| Detlefs | 952,912 | 4.14 (3.88–4.29) | 230k | 278 | 1.76 | 2.41× | 321 |
| FastPaxos | 25,617 | 3.28 (3.10–3.38) | 8k | 175 | 1.38 | 2.35× | 359 |
| TLCSailfish1 | 109,604 | 11.27 (11.16–11.57) | 10k | 146 | 3.60 | 3.11× | 203 |
| MCabs | 349 | 11.24 (11.03–11.43) | 31 | 33 | 3.47 | 3.37× | 73 |
| GameOfLife | 65,536 | 1.22 (1.20–1.31) | 54k | 47 | 0.39 | 3.18× | 87 |
| BufferedRandomAccessFile | 3,316 | 1.64 (1.61–1.70) | 2k | 33 | 0.53 | 3.01× | 33 |
| StarkMutex, N = 4 | 399,763 | 9.49 (9.40–10.22) | 42k | 587 | 12.70 | **0.73×** | 666 |
| cf1s_folklore | 2,057,174 | 16.69 (16.27–17.31) | 123k | 548 | 13.48 | 1.26× | 933 |
| SpanTreeRandom | 79,550 | 2.54 (2.43–2.62) | 31k | 89 | 1.35 | 2.00× | 94 |
| 2PCwithBTM | 1,245 | 0.017 (0.014–0.018) | — | 33 | 0.012 | — | 33 |

Every run agreed with TLC's recorded verdict and counts where `expected.json` has them. The
spread between runs is within 5% on every model of a second or more. The 4-thread build's CPU time
is 1.30× the one-thread CPU time in geomean, so a quarter of the threads' work is overhead.

SpanTreeRandom draws with RandomElement, so its counts depend on the seed. The suite now passes the
differential's `-seed 4` to every checker. The row above is at the binary's default seed 0. At
seed 4, one run takes 2.05 s for 65,396 states.

### Against TLC

TLC built from d8fb231 (the recordings' commit), run once each with `-workers 1` and with
`-workers auto` (4 here), on the same machine and with the same options. The native column is the
5-run median above, at seed 4 for SpanTreeRandom.

| Model | TLC, 1 | TLC, auto | Native, 1 | Over TLC, 1 | Over TLC, auto | TLC RSS MB |
|---|---:|---:|---:|---:|---:|---:|
| MCExactInitialSync | 126.44 | 81.11 | 17.24 | 7.3× | 4.7× | 2,106 |
| PaxosCommit | 110.73 | 35.74 | 27.23 | 4.1× | 1.3× | 1,817 |
| MCMultiNode | 65.37 | 20.10 | 7.79 | 8.4× | 2.6× | 1,706 |
| MCLamportMutex | 12.34 | 8.02 | 3.08 | 4.0× | 2.6× | 1,580 |
| MCbtree | 28.55 | 10.28 | 0.90 | 31.7× | 11.4× | 1,563 |
| Detlefs | 28.49 | 12.55 | 4.14 | 6.9× | 3.0× | 1,783 |
| FastPaxos | 29.00 | 8.35 | 3.28 | 8.8× | 2.5× | 1,481 |
| TLCSailfish1 | 36.26 | 10.97 | 11.27 | 3.2× | 1.0× | 1,637 |
| MCabs | 44.08 | 14.13 | 11.24 | 3.9× | 1.3× | 1,455 |
| GameOfLife | 9.64 | 3.68 | 1.22 | 7.9× | 3.0× | 1,459 |
| BufferedRandomAccessFile | 41.68 | 11.60 | 1.64 | 25.5× | 7.1× | 1,474 |
| StarkMutex, N = 4 | 104.50 | 32.36 | 9.49 | 11.0× | 3.4× | 1,950 |
| cf1s_folklore | 165.97 | 49.71 | 16.69 | 9.9× | 3.0× | 2,074 |
| SpanTreeRandom | 29.45 | 9.64 | 2.05 | 14.4× | 4.7× | 1,507 |
| 2PCwithBTM | 0.66 | 0.61 | 0.017 | 38.5× | 35.8× | 151 |

Geomean: the binary on one worker is 9.2× TLC on one worker, but only 3.5× TLC on every core,
since `-workers auto` gives TLC its threads and not the binary. With the 4-thread build, it is
6.3× TLC on every core over the 13 models that build measured. PaxosCommit, TLCSailfish1 and
MCabs are the models closest to TLC: on one worker TLC is within 4× of the binary, and on four
cores within 1.3×.

## Where the time goes

`perf record` (cpu-clock sampling at 499 Hz, frame pointers, a build with line tables) on one
thread. Self time, as a share of the run:

| Area | Share | Where |
|---|---|---|
| Liveness checker | 66% StarkMutex, 15% cf1s | `tla_live::checker`: `add_state` 12%, `evaluate` 22%, `find_violation` 11%, `answer` 7% (StarkMutex) |
| Answering liveness atoms | 27% StarkMutex, 58% cf1s | `tla_engine::live::answer_atoms`, one thread: the search records a graph |
| Set membership | 60% TLCSailfish1 | `member_test` → `Store::compare`/`compare_functions`: a binary search with TLC's comparison over sets of records |
| Memo tables | 38% MCMultiNode, 23% PaxosCommit, 20% MCLamportMutex | `memo_lookup::with<4>`: 84% of its samples on the first load of the row, a miss to memory |
| Symmetry | 55% FastPaxos, 35% Detlefs, 22% CheckpointCoordination and OptimizedCommitTS, 15% MultiPaxos | `Canonicalizer::canonicalize`/`permute`, and 7% (FastPaxos) in SipHash, from the permutations kept as `HashMap<Id, Id>` |
| Fingerprints | 27% MCbtree, 18% MCExactInitialSync, 12–16% elsewhere | `shift_by_table`, `get_child` |
| State table | 6–11% | `States::find`, a miss to memory per successor |
| Interning | 25% MCabs, 11% cf1s | `intern_block`/`find_in_block`: hashing and comparing whole blocks of long sequences |
| Walker dispatch | 11–13% MCExactInitialSync, MCbtree | `segment`, `exists_step` |
| Start-up | 49% of 2PCwithBTM's 17 ms | `native_front`: lowering 28%, SANY's report 21%, each parsing on its own |

On four threads:
- **Liveness gets slower.** StarkMutex goes from 9.5 to 12.7 s. When the atoms are answered on
  helper threads, `answer_atoms` evaluates every state's subscript on the main thread first, for
  each action atom (`subscript_value`, 27% of the run), where one thread evaluates only the states
  it asks about.
- **The search of a model that records a graph stays on one thread** (parallel.md), so StarkMutex's
  and cf1s's searches don't scale at all.
- **Memory grows with threads.** PaxosCommit goes from 744 MB to 2.1 GB: each thread keeps an
  overlay copy of the store and its own memo tables (speed.md, "Memory of the parallel search").

## Plan, ranked

Each item has its measured share, the gain expected, its risk to byte-identical output, and what
it depends on. Items marked independent can go to separate hill-climbers at once. Gains are on
this 4-core machine.

### 1. Threads in the binary (`perf-threads`)

Set `Settings.threads` from `-workers`, at most the cores, as the N-API binding does with
`PROVE_IT_WORKERS`. Fix the liveness regression first: compute each subscript's values once
across atoms, on the helpers, and only for the states asked about.
- **Gain:** measured 1.85–3.4× on the 13 models without a recorded graph, geomean about 2.4× at 4
  threads. More on 16 cores (Benchmark on `depot-ubuntu-24.04-16`).
- **Risk:** low. The shared levels already give one thread's states, counts, checkpoints and
  state logs (parallel.md, tested at 1, 2, 4 and 16 threads), and the banner already prints
  `-workers`. Parity runs `-workers 1`, so the PR adds a differential pass at 4 workers whose
  only expected difference from the recording is the banner's worker count (normalized), or the
  coordinator runs Parity with `PROVE_IT_WORKERS=4`.
- **Depends on:** nothing. Everything below then measures at 1 and 4 workers.
- **As built.** `-workers N` sets the threads (`auto` is every core); `PROVE_IT_WORKERS`
  overrides it, so Parity also runs the native differential on four threads under the recordings'
  `-workers 1`. The atoms' helpers evaluate a step's subscript only for the states asked about.
  Turning threads on found three faults on the threaded paths, fixed first (#171): helpers that
  computed the startup's definitions again (SpanTreeRandom's `Edges`, drawn), atoms on helpers
  where something draws or uses TLC's registers, and a shared level that stopped and kept no trace.
  On the suite, `-workers 4` against `main` on one worker, medians of 5 runs on the 4-core
  container:

  | Model | `main`, 1 | 4 threads | Speedup | RSS MB |
  |---|---:|---:|---:|---|
  | MCExactInitialSync | 17.19 | 8.76 | 1.96× | 1,093 → 1,328 |
  | PaxosCommit | 26.81 | 10.43 | 2.57× | 744 → 2,120 |
  | MCMultiNode | 7.39 | 3.14 | 2.36× | 539 → 1,117 |
  | MCLamportMutex | 2.83 | 1.41 | 2.01× | 143 → 194 |
  | MCbtree | 0.91 | 0.45 | 2.05× | 50 → 73 |
  | Detlefs | 4.05 | 1.65 | 2.46× | 278 → 322 |
  | FastPaxos | 3.08 | 1.39 | 2.22× | 175 → 360 |
  | TLCSailfish1 | 11.14 | 3.55 | 3.14× | 146 → 205 |
  | MCabs | 11.44 | 4.20 | 2.72× | 35 → 73 |
  | GameOfLife | 1.16 | 0.40 | 2.86× | 47 → 87 |
  | BufferedRandomAccessFile | 1.56 | 0.48 | 3.25× | 35 → 35 |
  | StarkMutex, N = 4 | 8.08 | 8.18 | 0.99× | 588 → 678 |
  | cf1s_folklore | 16.01 | 13.21 | 1.21× | 547 → 943 |
  | SpanTreeRandom | 2.00 | 2.01 | 1.00× | 71 → 71 |
  | 2PCwithBTM | 0.012 | 0.011 | — | 35 → 35 |

  Geomean 1.98× over the suite and 2.4× over the eleven models without a recorded graph. Every
  run agrees with TLC. On one worker the branch is `main`'s speed (1.00×). The liveness models
  stay near one thread: their search records a graph and runs on one thread, and SpanTreeRandom's
  atoms draw. That is track 2's and track 6's work, as is the memory four threads take.

  On 16 cores (`depot-ubuntu-24.04-16`, AMD EPYC 9R45), the Benchmark workflow on this branch at
  419c7eb, medians of 3 runs, with TLC at d8fb231 on the same machine. MCExactInitialSync didn't
  run: the workflow didn't fetch its corpus (#180).

  | Model | 1 thread | 16 threads | Speedup | TLC, 16 workers | Over TLC, 16 | RSS MB, 1 → 16 |
  |---|---:|---:|---:|---:|---:|---|
  | PaxosCommit | 22.70 | 3.28 | 6.9× | 10.33 | 3.1× | 744 → 3,227 |
  | MCMultiNode | 6.14 | 1.07 | 5.7× | 6.82 | 6.4× | 538 → 1,851 |
  | MCLamportMutex | 2.26 | 0.58 | 3.9× | 3.44 | 5.9× | 141 → 385 |
  | MCbtree | 0.71 | 0.21 | 3.4× | 3.94 | 18.8× | 50 → 123 |
  | Detlefs | 3.27 | 0.71 | 4.6× | 5.07 | 7.1× | 279 → 379 |
  | FastPaxos | 2.82 | 0.46 | 6.1× | 2.69 | 5.8× | 175 → 1,280 |
  | TLCSailfish1 | 9.12 | 0.93 | 9.8× | 3.16 | 3.4× | 146 → 482 |
  | MCabs | 10.64 | 1.37 | 7.8× | 3.63 | 2.6× | 35 → 205 |
  | GameOfLife | 1.27 | 0.16 | 7.9× | 1.58 | 9.9× | 47 → 219 |
  | BufferedRandomAccessFile | 1.53 | 0.17 | 9.0× | 3.46 | 20× | 37 → 69 |
  | StarkMutex, N = 4 | 7.35 | 6.62 | 1.11× | 12.96 | 2.0× | 589 → 759 |
  | cf1s_folklore | 13.81 | 11.36 | 1.22× | 15.12 | 1.3× | 545 → 2,233 |
  | SpanTreeRandom | 1.79 | 1.77 | 1.0× | 3.32 | 1.9× | 71 → 71 |
  | 2PCwithBTM | 0.01 | 0.01 | — | 0.48 | — | 38 → 38 |

  The models with large levels and costly states scale best (TLCSailfish1, BufferedRandomAccessFile,
  GameOfLife, MCabs: 7.8–9.8×); those with cheap states scale least (MCbtree, MCLamportMutex), as
  the serial merge of each level takes a larger share. Memory grows with the threads, by up to
  150 MB a thread on PaxosCommit and 70 MB on FastPaxos: each thread keeps a copy of the store in
  its overlay, its own memo tables and, under SYMMETRY, its own canonicalizer's tables of images,
  each sized to the store. Both are track 6's.

### 2. Liveness (`perf-liveness`), independent

Liveness models spend 73–93% of their time in liveness, on one thread.
- (a) **Bit-parallel consistency.** A tableau node's state predicates are conjunctions of atoms
  answered in tables. Precompute each state's atoms as a bit row and each node's literals as a
  mask and a value, so `is_consistent` is a mask compare instead of `evaluate`'s tree walk. The
  same for each step's action checks.
- (b) **Share the levels of a search that records a graph.** The merge already walks the
  candidates in (parent, step) order. It would also append each parent's edges, duplicates
  included, in that order.
- (c) **Behaviors and atoms in parallel.** Each behavior graph is built independently of the
  others, and `find_violation`'s SCC searches can run one per behavior.
- **Gain:** 2–4× on StarkMutex and cf1s.
- **Risk:** medium. The node numbering, the order the cycle search meets nodes, and therefore the
  counterexample, must stay TLC's. (a) and (c) change only how answers are computed. (b) must
  number edges exactly as one thread does.

### 3. Membership without comparing (`perf-membership`), independent

TLC's `SetEnumValue.member` is a binary search with `compareTo` (`ValueVec.search`), which the
store reproduces, errors included. Equal values have equal ids, so where no comparison on the
search's path can fail (the element and the set's elements of a kind and shape that compare
without error, which the store can mark when it interns), membership is an id lookup: a sorted
array of the set's ids, built when a large set is first tested.
- **Gain:** TLCSailfish1 about 2×. GameOfLife, Detlefs and FastPaxos also spend 10–25% in
  `compare`.
- **Risk:** medium: which comparisons TLC fails on must be read from `compareTo` of every value
  class, not assumed. Where in doubt, the comparing path stays.

### 4. Memo tables that miss less (`perf-memo`), independent

84% of the lookup's time is the first load. Options, to be measured in this order:
- a tag array of 8-bit hashes, probed first, so a miss reads one line of tags and no row;
- a size cap, past which a table evicts (direct-mapped) instead of growing past the cache;
- probation on cost: switch a table off where its inner evaluation is cheaper than the miss.
- **Gain:** 10–30% on MCMultiNode, PaxosCommit and MCLamportMutex.
- **Risk:** none to output. The tables are caches of pure functions, and ToString's ranking and
  TLCCache already keep their own rules.

**Done (#179): clustering.** The hot tables key on one state variable and the bound names of a
quantifier over it (PaxosCommit `[msgs, s28, s29, s31]`, MCMultiNode `[history, s72, s73]`), and
fill the 4M-entry cap. A table of two keys or more, once it has 4,096 slots, homes an entry by a
hash of its first key alone, so a state's entries share one run. A probe budget (32 a lookup over
a window of 16,384 lookups) scatters a table whose first key has too few values.
- PaxosCommit 34.4 → 28.4 s, MCMultiNode 9.3 → 7.7 s (1.21× each). The rest of the suite is within
  noise.
- Memo is then about 24% of MCMultiNode and 12% of PaxosCommit. 40% of what is left of the lookup
  is still the first load of a run: the first lookup of a key never seen.

Measured and dropped:
- **A size cap without eviction** (2^12 to 2^20 entries): slower on both. The caching pays even at
  a miss to memory.
- **Clustering in bands** of 8 or 64 slots instead of on the first key alone: slower than both.
- **Clustering from the start**, small tables included: TLCSailfish1 9% slower, and MCLamportMutex
  3.4 → 4.4 s without the probe budget.
- **Prefetching each large table's run when a state becomes current** (`set_current`):
  MCMultiNode 5% slower.
- **A memo keyed per action footprint** (item 3 of "What 10x would take"): not built. Its hit
  rate's ceiling is the share of expansions whose read variables repeat. PaxosCommit's costly
  actions (Phase1a, Phase2a, Decide) read only `msgs`, which is new in 848K of 1.2M expansions:
  at most about 30% hits, so at most about 15% of the run, before the cost of recording and
  replaying successors. MCMultiNode's `history` is new in 481K of 1.4M expansions, and the work
  keyed by it is already in tables keyed on `history` (the invariants hit 92% at width 1).

### 5. Symmetry (`perf-symmetry`), independent

- Keep each permutation as a dense table by id instead of a `HashMap` with SipHash: 7% on
  FastPaxos at once.
- Then cut `canonicalize`'s per-permutation work: compare images variable by variable against the
  best so far with early exit (already done), and order the permutations so the representative is
  found early.
- **Gain:** 1.2–1.8× on the symmetric models.
- **Risk:** low. The representative must stay the least image in TLC's order.

### 6. Thread efficiency and memory (`perf-scaling`), after 1

At four threads, a quarter of the CPU time is overhead, and memory triples on PaxosCommit. The
known costs (parallel.md, speed.md):
- the serial merge, 10–25% of a level;
- threads spawned per level;
- per-thread overlays and cold memo tables.

The candidates are kept threads, a merge that imports while the next level expands, and shared
read-only memo snapshots.
- **Needs:** the 16-core Benchmark from the coordinator to measure scaling.
- **Gain:** from 2.4× toward 3.5× at 4 threads, and more at 16.
- **Measured (`perf` at 4 threads).** On MCExactInitialSync the merge runs alone for about 3.5 s
  of the 9.7 s: 14% of all samples, of which half is `States::find`, the state table's probe
  missing the cache on each candidate, then `insert` and `Store::import`. On PaxosCommit the
  threads' own work dominates, and `forget_from` at each level costs 2%.
- **Done: the merge reads the table ahead.** It touches the home slot of the candidate 16 places
  on before it probes for the current one. MCExactInitialSync at 4 threads: 9.15 → 8.36 s
  (medians of 9, ranges 8.66–9.58 and 8.07–9.09). Neutral where the table fits the cache
  (MCbtree, Detlefs). One thread doesn't merge.
- **Done: the threads fill the table.** After the threads expand a level, they fill the state table
  too: each owns a range of its slots, split by the fingerprint's top bits (the home slot), and
  walks the level's candidates in (parent, step) order, probing and inserting those whose home is in
  its range. The merge then only numbers and imports the new states; a fingerprint whose probe runs
  past its thread's range, and 0, it probes itself, in order as before. That takes a table without
  indices, which is the binary's (no fingerprint verification), no graph recorded, and no invariant
  deferred to the merge (a VIEW or SYMMETRY whose new state fails one); those still merge serially. On 4 cores, medians
  of 5 interleaved runs at 4 threads against `perf-state-table`, every count unchanged:
  MCExactInitialSync 7.63 → 7.08 s (−7%), MCbtree 0.398 → 0.371 (−7%), MCMultiNode 2.75 → 2.62
  (−5%), PaxosCommit 9.02 → 8.66 (−4%), Detlefs 1.13 → 1.09 (−4%). The rest is within noise
  (TLCSailfish1, FastPaxos and MCLamportMutex checked over 9 runs each), and the models that record
  a graph or run on one thread don't fill.
- **Measured, not done: growing the table on threads.** Doubling the table takes 220–350 ms at the
  last doubling on MCExactInitialSync, nearly all of it the kernel faulting in 4 KB pages
  (transparent huge pages are `madvise` on the machine measured). Threads rewriting ranges of it
  fault in parallel and contend: 0.6 s slower at 4 threads. With `MADV_HUGEPAGE` on the table it
  takes 55–120 ms and the run 7.21 → 6.25 s at 4 threads; that is track 8's next change.
- **Memory with threads, measured on PaxosCommit.** Each thread's overlay of the store holds about
  82 MB (meta 16 MB, heap 64 MB, its table 2 MB), against the base store's 16 MB table and the
  states' 40 MB. Reusing the level's candidate buffers from level to level changed neither peak RSS
  (2,135–2,158 MB against 2,074–2,187 MB) nor time. The rest is the memo tables each thread doubles
  (track 4's per-thread budget, #187) and what glibc keeps in each thread's arena once they free.
- **Measured, not done: an overlay that reads the base in place.** Rather than copy the store's
  values, blocks and texts, an overlay read those below its base's counts from the store itself.
  Peak RSS at 4 threads fell on PaxosCommit 1,427 → 1,202 MB, but one thread ran 11–15% slower
  (PaxosCommit 20.0 → 23.0 s, MCExactInitialSync 15.3 → 17.0 s), with the store's path out of line
  and cold: the test of which store holds a value, on every read in `compare_functions`,
  `find_in_block` and `compare`. Only a store generic over the two kinds would avoid it.
- **Measured, not done, each within noise at 4 threads:** prefetching a thread's own table of the
  level's states with the state table's; importing the values a thread computed once, a constant's,
  into the store after each level (they are nearly all computed at startup); inlining the lookup
  of a length's shift table. Keeping the threads from level to level isn't worth building: the
  suite's searches are at most 82 levels deep, a few milliseconds of starts.
- **Where the threads' time goes.** At 4 threads the threads take 50–64% more CPU than one thread
  does, spread evenly over evaluation, the memo tables, the store and the fingerprints: the cores
  contend for memory and cache, rather than any part doing more. Of what is the threads' own, their
  probes of the state table miss the TLB (track 8's huge pages), and each thread's memo tables and
  overlay are working sets of their own (track 4).
- **16 cores, `main` at d7c8b5d** (before #168, #183, #178 and #182), medians of 3, every run
  agreeing with TLC: one worker, then 16 threads.

  | Model | 1 thread | 16 threads | Speedup | RSS MB, 1 → 16 |
  |---|---:|---:|---:|---|
  | MCExactInitialSync | 12.86 | 3.68 | 3.5× | 1,093 → 1,694 |
  | PaxosCommit | 17.80 | 3.00 | 5.9× | 744 → 3,231 |
  | MCMultiNode | 4.43 | 1.03 | 4.3× | 538 → 1,812 |
  | MCLamportMutex | 1.76 | 0.54 | 3.3× | 141 → 392 |
  | MCbtree | 0.65 | 0.20 | 3.3× | 50 → 123 |
  | Detlefs | 3.20 | 0.69 | 4.6× | 279 → 379 |
  | FastPaxos | 2.54 | 0.48 | 5.3× | 175 → 1,278 |
  | TLCSailfish1 | 9.40 | 0.96 | 9.8× | 146 → 484 |
  | MCabs | 10.07 | 1.15 | 8.8× | 34 → 205 |
  | GameOfLife | 1.18 | 0.15 | 7.9× | 47 → 218 |
  | BufferedRandomAccessFile | 1.47 | 0.16 | 9.2× | 34 → 69 |
  | StarkMutex, N = 4 | 4.18 | 3.87 | 1.08× | 591 → 751 |
  | cf1s_folklore | 12.44 | 8.58 | 1.45× | 553 → 2,244 |
  | SpanTreeRandom | 1.61 | 1.61 | 1.0× | 71 → 71 |

  The run took 1.66× the CPU of one worker overall. The weak scalers are the models with a large
  state table and cheap states (MCExactInitialSync, MCbtree, MCLamportMutex), whose serial merge
  this track's fill shortens. Memory grows most on FastPaxos (7×: each thread's symmetry tables of
  images, 73 MB with 3% of their slots used, which #172's rows by id cut to 79 → 127 MB at 4
  threads), cf1s_folklore (4×) and PaxosCommit (4.3×; 2,566 MB with #187's budget).

### 7. Interning long blocks (`perf-intern`), independent

Appending to, or EXCEPT of, a long sequence hashes and compares the whole block. A hash that
updates by position (polynomial) makes the hash O(1) for a patch. Comparing on a hit stays
O(n), but hits with equal hashes are equal values in practice.
- **Gain:** MCabs and cf1s, 10–20%.
- **Risk:** none to output: ids are numbered in interning order, not by hash.

### 8. Fingerprints and the state table (`perf-fingerprint`), independent, lower

Batch a state's successors: compute their fingerprints, prefetch every home slot, then probe. The
earlier tries in speed.md (carry-less multiply, changed slots, 16-byte entries) found nothing, so
expect 5–10% on MCExactInitialSync and MCbtree.

### 9. Start-up (`perf-startup`), with the front-end session

SANY's report and the lowering each parse the spec and its modules. One parse shared between them
would cut the front end's part of a small run, about half of 17 ms, by up to half. The front-end
session owns `tla-front` and the CLI's front, so this goes to them or waits for their change to
land.

## What 10x would take

The plan above sums to roughly 3–5× on four cores: about 2.4× from threads, and the rest from
the single-thread items, each removing a share of one or two models' time. 10× over today means
removing about 90% of each model's single-thread time, threads aside, or 75% with 2.4× from
threads. Grouping the profiles' self time shows what is left once tracks 1–8 have done what they
promise.

Self time by category, one thread (`perf script` leaf frames grouped by symbol):

| Model | Successors/s | Evaluator dispatch | Memo | Compare | Intern, alloc, copy | Store reads | Fingerprints | State table | Symmetry |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| MCExactInitialSync | 2.3M | 30% | 8% | 0% | 11% | 5% | 19% | 21% | — |
| MCbtree | 3.1M | 32% | 4% | 6% | 9% | — | 27% | 16% | — |
| MCLamportMutex | 0.9M | 32% | 22% | 1% | 13% | 11% | 9% | 6% | — |
| MCMultiNode | 0.5M | 21% | 42% | 1% | 9% | 13% | 3% | 4% | — |
| PaxosCommit | 0.62M | 29% | 26% | 16% | 13% | 7% | 4% | 3% | — |
| Detlefs | 0.5M | 15% | 4% | 13% | 5% | 2% | 13% | 9% | 31% |
| FastPaxos | 98k | 11% | 4% | 18% | 4% | 2% | — | 1% | 50% |
| TLCSailfish1 | 28k | 9% | 11% | 68% | 6% | 4% | — | 1% | — |
| MCabs | 520 | 35% | 4% | 5% | 31% | 23% | — | — | — |
| GameOfLife | 107k | 37% | 6% | 27% | 16% | 8% | — | 1% | — |
| BufferedRandomAccessFile | 79k | 59% | 17% | 7% | 5% | 7% | 1% | — | — |

Why PaxosCommit, TLCSailfish1 and FastPaxos are slow:
- **They don't reach states slowly; each successor costs more.** MCExactInitialSync makes 2.3M
  successors a second, PaxosCommit 0.62M, FastPaxos 98k and TLCSailfish1 28k.
- **PaxosCommit's actions quantify over the set of messages** and build sets per successor.
  `compile_subset`, `compile_record_set`, `union` and `merge` are on its hot path, and `member_test`
  takes 14%. A third of its time is set algebra and membership, and a quarter memo misses.
- **TLCSailfish1** spends 60% in `member_test`, which compares records field by field down a binary
  search of a large set.
- **FastPaxos** spends 50% in symmetry: each successor is canonicalized under every permutation,
  and each permutation rebuilds the image of the message set.

So the evaluator's dispatch, the closures' own cost, is not what makes them slow. It is 9–29% of
those three. Value work per successor is. The fast models are the other way round: dispatch,
fingerprints and the state table make up 70–80% of MCExactInitialSync and MCbtree, and value work
is small there.

The design-level changes, ranked by the share they attack:

1. **Values that answer set questions without comparing**, beyond track 3. A set interned with an
   id-indexed side table, or a hash of its ids, answers `\in`, `\subseteq`, union with one element
   and `\ ` by id, wherever the store can show no comparison would fail. Comparing in TLC's order
   is then kept for sorting new sets.
   - Attacks compare plus part of intern: 68% of TLCSailfish1, 30% of GameOfLife, about 30% of
     PaxosCommit, and 18% of FastPaxos.
   - Expected: 2–3× on those.
2. **Symmetry by orbit, not by permutation.** TLC's representative is the least image over the
   group. Sorting the model values by an invariant of the state (their counts in each variable,
   say) narrows the permutations that can give the least image before any is built.
   - The group's images then cost a few comparisons instead of the whole group, and the chosen
     representative must still be checked to be TLC's.
   - Attacks 31–50% on Detlefs and FastPaxos, and about 20% on the large symmetric models.
3. **Memo by footprint at the action, not by expression.** PaxosCommit's and MCMultiNode's memo
   tables miss to memory because each successor asks many small tables with keys they have never
   seen. A guard memoized on the variables it reads would be a hit for every successor that
   didn't change them.
   - Today's tables key on the variables an expression reads. Keying each action's enabledness on
     the parent's id-tuple of the variables it reads is coarser, and hits when an action fires
     from states differing only elsewhere.
   - Attacks the 22–42% memo share: expected 1.3–1.6× on MCMultiNode, PaxosCommit and
     MCLamportMutex.
   - Measured after #179 and dropped: at most about 30% hits on PaxosCommit (item 4 above).
4. **Incremental fingerprints and a compact state table**, for the fast models. A successor's
   fingerprint can be the parent's, updated for the variables its action assigned.
   - `changed-slots` (speed.md) tried skipping comparisons and lost. This instead skips the
     fingerprint work for unchanged variables, which is 19–27% on MCExactInitialSync and MCbtree.
   - A table that stores fingerprints and indices in one cache line per probe, plus batched
     prefetch, attacks the 16–21% state table share.
   - Expected 1.3–1.5× on the fast models.
5. **Specialised walks.** The remaining dispatch, 30% of the fast models and 59% of
   BufferedRandomAccessFile, is closure entry and exit and the walker's bookkeeping, per
   speed.md's callgrind. native-backend.md measured a native backend at 25–45% of instructions,
   and it is shelved.
   - A middle way is closures generated per action shape for the PlusCal `pc` dispatch, the most
     common walk (#137), fusing a whole `pc = l /\ ... /\ pc' = m` step into one closure. That
     spends no unsafe and no executable memory.
   - Expected 1.2–1.4× where dispatch dominates.
6. **Scaling past four cores** (track 6): a lock-free fingerprint set, threads kept across
   levels, and the merge overlapped with expansion. TLC itself scales about 3× from 1 to 4
   workers on these models.
   - The 16-core Benchmark decides how much is left. 10× from threads alone would need about 16
     cores at 60% efficiency.

Per model, the path to 10× is then: threads (2–3× at 4 cores, more at 16), times the one or two
design items that attack its largest category (1.5–3×), times what the rest removes (1.2–1.5×).
That reaches 10× on four cores only where one category is most of the time: TLCSailfish1,
FastPaxos, Detlefs, PaxosCommit and the liveness models. On the fast models (MCExactInitialSync,
MCbtree) it needs more cores. These items are independent of each other and of tracks 2–8, except
1 with 3 (membership) and 3 with 4 (memo): those are one track each.

### Not on the list

- A JIT or native code: the backend is shelved (native-backend.md), and the workspace stays std
  only.
- Hashing ids with a cheaper hash in the state table: it is already a multiply-shift.

## Results

Each change, measured with the suite against the build before it: median wall seconds of 5
interleaved runs on the 4-core cloud container, with the min–max range. Models not listed moved
within their range.

### The suite again at 3f66319

`main` at 3f66319, the same container, `bench-suite.ts` with `native` (one worker) and
`native-auto` (4 threads): median wall seconds of 5 interleaved runs, with the min–max range. TLC
is the baseline's single run of each (d8fb231, the same container), not run again. Every run agrees
with TLC. MCabs, GameOfLife, BufferedRandomAccessFile, StarkMutex and cf1s_folklore were run again
on an idle machine, since a build overlapped their first runs.

| Model | Baseline, 1 worker | Now, 1 worker (range) | Gain | Now, 4 workers (range) | Over TLC, 1 | Over TLC, auto (4) |
|---|---:|---:|---:|---:|---:|---:|
| MCExactInitialSync | 17.24 | 15.47 (15.15–16.20) | 1.11× | 6.85 (6.78–7.38) | 8.2× | 11.8× |
| PaxosCommit | 27.23 | 18.48 (17.19–19.49) | 1.47× | 8.45 (7.87–8.79) | 6.0× | 4.2× |
| MCMultiNode | 7.79 | 5.75 (5.56–5.99) | 1.35× | 2.65 (2.53–2.95) | 11.4× | 7.6× |
| MCLamportMutex | 3.08 | 2.45 (2.31–2.91) | 1.26× | 1.28 (1.14–1.39) | 5.0× | 6.3× |
| MCbtree | 0.90 | 0.83 (0.81–0.85) | 1.09× | 0.39 (0.37–0.39) | 34.5× | 26.4× |
| Detlefs | 4.14 | 2.57 (2.41–2.82) | 1.61× | 1.15 (1.10–1.21) | 11.1× | 11.0× |
| FastPaxos | 3.28 | 1.79 (1.62–1.85) | 1.83× | 0.84 (0.82–0.98) | 16.2× | 10.0× |
| TLCSailfish1 | 11.27 | 3.47 (3.38–3.78) | 3.25× | 1.23 (1.19–1.30) | 10.5× | 8.9× |
| MCabs | 11.24 | 10.18 (9.73–11.16) | 1.10× | 3.06 (2.90–3.20) | 4.3× | 4.6× |
| GameOfLife | 1.22 | 1.25 (1.21–1.29) | 0.97× | 0.41 (0.39–0.44) | 7.7× | 9.0× |
| BufferedRandomAccessFile | 1.64 | 1.64 (1.61–1.67) | 1.00× | 0.54 (0.50–0.56) | 25.4× | 21.6× |
| StarkMutex, N = 4 | 9.49 | 5.41 (4.71–5.66) | 1.76× | 3.61 (3.30–4.23) | 19.3× | 9.0× |
| cf1s_folklore | 16.69 | 16.07 (14.70–17.13) | 1.04× | 9.37 (8.79–10.48) | 10.3× | 5.3× |
| SpanTreeRandom (seed 4) | 2.05 | 1.93 (1.91–2.01) | 1.06× | 1.99 (1.81–2.07) | 15.2× | 4.8× |
| 2PCwithBTM | 0.017 | 0.011 (0.011–0.012) | 1.55× | 0.011 (0.011–0.011) | 60.0× | 55.5× |

Over the 14 models past 2PCwithBTM, whose 10–17 ms is start-up, in geomean: one worker is 1.34×
the baseline, 4 threads are 2.15× one thread, one worker is 11.2× TLC on one worker (9.2× at the
baseline), and 4 threads are 8.6× TLC on every core (3.5×).

### 16 cores at de3a9f8

`main` at de3a9f8 on `depot-ubuntu-24.04-16` (AMD EPYC 9R45), the Benchmark workflow, medians of
3 runs: one thread, then 16, with the CPU seconds at 16 and the peak RSS.

| Model | 1 thread, s | 16 threads, s | Speedup | CPU at 16, s | RSS MB, 1 → 16 |
|---|---:|---:|---:|---:|---|
| MCExactInitialSync | 12.22 | 1.95 | 6.3× | 19.6 | 901 → 1,446 |
| PaxosCommit | 14.93 | 2.61 | 5.7× | 36.0 | 719 → 2,660 |
| MCMultiNode | 4.41 | 0.86 | 5.1× | 9.2 | 522 → 1,690 |
| MCLamportMutex | 1.80 | 0.48 | 3.8× | 4.9 | 136 → 378 |
| MCbtree | 0.66 | 0.17 | 3.9× | 1.16 | |
| Detlefs | 1.73 | 0.44 | 3.9× | 2.86 | |
| FastPaxos | 1.36 | 0.27 | 5.0× | 3.11 | |
| TLCSailfish1 | 2.98 | 0.40 | 7.5× | 4.87 | |
| MCabs | 9.12 | 1.14 | 8.0× | | |
| GameOfLife | 1.31 | 0.16 | 8.2× | | |
| BufferedRandomAccessFile | 1.53 | 0.17 | 9.0× | | |
| StarkMutex, N = 4 | 3.29 | 2.13 | 1.5× | 7.5 | |
| cf1s_folklore | 12.48 | 5.51 | 2.3× | 47.7 | 559 → 2,251 |
| SpanTreeRandom | 1.69 | 1.66 | 1.0× | | |

Geomean 4.3×. Against d7c8b5d, MCExactInitialSync rose from 3.5× to 6.3×, cf1s_folklore from 1.45×
to 2.3× and StarkMutex from 1.08× to 1.5×. Detlefs (4.6× → 3.9×) and TLCSailfish1 (9.8× → 7.5×)
fell because one thread got faster.

Two limits show. PaxosCommit takes 36 CPU seconds at 16 threads for 14.9 s of one thread's work,
and cf1s_folklore 47.7 for 12.5: the cores contend for memory. MCbtree, Detlefs and MCLamportMutex
stop near 3.9× with CPU only 1.6–2.7× one thread's: a serial part limits them. An instrumentation
build timed the parts at 4 threads on the 4-core container:

| Model | Wall, ms | Threads expanding | Merge after the threads | Levels on one thread |
|---|---:|---:|---:|---:|
| MCbtree | 342 | 257 | 53 (15%) | 28 (13 levels, 7,581 states) |
| Detlefs | 1,121 | 758 | 295 (26%) | 53 (33 levels, 15,623 states) |
| MCLamportMutex | 1,259 | 1,069 | 157 (12%) | 26 (18 levels, 2,104 states) |
| PaxosCommit | 8,468 | 7,867 | 553 (6.5%) | 15 |
| MCExactInitialSync | 6,747 | 5,263 | 1,439 (21%) | 10 |

The merge doesn't shrink with the threads, so at 16 it is most of what is left: on Detlefs about
300 ms against about 190 ms of expansion. Its time on the search thread, profiled on Detlefs:
`Store::import` 18%, the merge's own loop 18%, the kernel 25% (page faults and the page-table locks
of the vectors and table that grow, the states' arrays and the state table), copying 5% and the
table's growth 4%. Keeping freed memory in the allocator (`glibc.malloc.mmap_threshold`,
`trim_threshold`) changed nothing, so the faults are memory that is new, which huge pages for the
state table (PR 199) address.

**A parallel merge, bounded.** Its parts at 4 threads, on the search thread:

| Model | Kernel | Import | Merge loop | Fill and growth | Copying | Other |
|---|---:|---:|---:|---:|---:|---:|
| MCbtree | 31% | 7% | 9% | 8% | 4% | 40% |
| Detlefs | 25% | 18% | 18% | 4% | 5% | ~30% |
| MCLamportMutex | 25% | 23% | 14% | 7% | 11% | 21% |
| MCExactInitialSync | 42% | 12% | 21% | 14% | 6% | 5% |

Threads could take only the import, the loop and the copying: page faults on one address space
serialize on its locks, as the table grown on threads showed. Projected to 16 threads (the serial
part scaled from the 4-core split, the rest the 16-core wall less it), a merge on threads would
take MCbtree from 170 to about 156 ms (1.09×), Detlefs 440 → 340 (1.29×), MCLamportMutex
480 → 419 (1.15×) and MCExactInitialSync 1,950 → 1,487 (1.31×). Its first step, the states'
arrays reserved for the level's new states before the merge, with or without `MADV_HUGEPAGE`, was
within noise at 4 threads (MCExactInitialSync 6.81 / 6.76 / 7.47 s, Detlefs 1.13 / 1.15 / 1.16,
MCbtree 0.370 / 0.377 / 0.368, MCLamportMutex 1.25 / 1.25 / 1.25). Not built: the store's import
rewritten for at most 1.3×. Huge pages on the state table, which cut the kernel's part, come first.

### Membership by id (plan item 3)

The store gives each value a shape (`tla-values/src/store/shapes.rs`): a class of values any two
of which TLC compares without failing, read from `compareTo` of each value class at d8fb231.
Where the element's shape joins the shape of the set's elements, no comparison of TLC's search can
fail, so the store answers by the element's id; elsewhere it compares as before. The value oracle
(5 seeds of 200,000 operations) answers as the TypeScript store does on every operation and finds
no failure of TLC's that the store misses.

| Model | Before, s | After, s | Speedup |
|---|---|---|---:|
| TLCSailfish1 | 16.64 (16.33–17.02) | 5.13 (5.11–5.40) | 3.24× |
| PaxosCommit | 35.45 (34.35–36.91) | 33.30 (32.76–33.53) | 1.06× |
| MCabs | 18.34 (17.77–18.71) | 17.48 (16.92–17.64) | 1.05× |

### Function application by id

TLC finds a key in a function's domain by a binary search with `compareTo` (`FcnRcdValue.select`)
or a scan with `equals`. Where the key's shape joins the class of the function's keys, neither can
fail, so the store finds the key's id in a domain of up to 256 keys instead of comparing. GameOfLife
applies a function over 36 tuple keys 128 times a state. Measured against main fb05e28, one worker:

| Model | Before, s | After, s | Speedup |
|---|---|---|---:|
| GameOfLife | 1.50 (1.47–1.64) | 1.20 (1.13–1.31) | 1.25× |

MCabs spends a similar share in `find_in_block`, but on functions of a few model-value keys, which
the store already scans by id: its cost is the misses of reading their values, which this doesn't
change.

### Liveness (`perf-liveness`)

The track ends with StarkMutex at about 4.7 s on one worker, from 9.49 s at the baseline. The last
step answers ENABLED of TLC's actions from the steps the search took (#203): 5.37 → 4.72 s on one
worker and 3.83 → 2.87 s on four. Where the 4.7 s goes, at main d89e559 (instrumented, 3 runs):
answering the atoms 1.53 s, the checker 2.20 s (adding states about 1.7 s of it), and the search
and start-up about 0.95 s.

Two further steps were bounded and not built, since neither clears 1.1× by a safe margin:

| Idea | Bound on StarkMutex, one worker | Why it stops there |
|---|---|---|
| Label the steps in the walk of the next-state relation, not by walking TLC's 65 actions one by one | at most 0.5 s: 4.70 → 4.20 s, 1.12×; about 1.08–1.10× once the labels cost anything | The unlabelled search took 0.45 s before #203 and the labelled one takes about 0.95 s. Each label must be the action TLC's split gives the step, through `\E` over constant sets and operator bodies, for every (action, successor) pair. |
| A flat form of the 60 action checks the checker evaluates as it adds states | 0.3–0.5 s of `add_states`' 1.7 s: 1.07–1.12× | Most of `add_states` is reading the answer tables and building the behavior graphs, which the flat form leaves. |

Together they bound StarkMutex at about 1.25×.

## Measured and dropped

Tried on the symmetry and evaluator tracks, measured with the suite on the 4-core container, and
dropped because they did not move it. Recorded so that nobody repeats them.

| Idea | Model | Result | Why it lost |
|---|---|---|---|
| Scan a small set's parts instead of marking them in a table by id (`compare_parts`) | FastPaxos | 2.33/2.41 s before, 2.40/2.35 s after | The marks were not the cost the profile attributed to them. |
| Fingerprint the symmetric representative incrementally from its parent's (`get_child` on the canonical keys) | Detlefs | 2.7–2.9 s → 3.2–3.5 s | Canonicalizing the parent again, or reading its key back, costs more than the shifts saved. The canonical keys of a parent and its successors often differ in many slots. |
| Skip the step memo for values the symmetry group fixes | Detlefs | 3.05/3.08 s → 3.21/3.28 s | Few of Detlefs' 31 variables are fixed, and the extra test costs on every variable. |
| Rank the orbit images of a set's parts once per step miss and compare permutations by integer ranks | FastPaxos | Estimated only: about 40 µs per miss against about 20 µs today | Sorting the images takes 100–200 record comparisons per miss. |
| A table from label to walks for PlusCal's `switch` (string labels compare by id) | Detlefs | 4.70 → 4.63 s, within noise | The `switch`'s self time is the walks inlined into it, not the 49-label scan. |
| An index, per (quantifier, set id), of the elements whose leading `m.f = c` holds | PaxosCommit | 33.1–35.0 s → 36.0–37.0 s | `msgs` is a new set in nearly every state, so the index is used only by that state's 3 acceptor scans. |
| Fuse a whole PlusCal step into one closure | MCbtree, MCExactInitialSync | Not built: estimated 5–10% | `walker::segments`' self time is spread over the per-op dispatch, 1–2% a line, with no hot spot. |
| Cache membership in a set that reads nothing (a type's record sets) by the element | PaxosCommit, MCExactInitialSync | PaxosCommit 21.85 → 21.63 s; MCExactInitialSync 18.41 → 20.94 s, 190 MB more | `msgs \in SUBSET Message` falls from 14% to 1% of the profile but not in wall time, and the tables of elements cost the fast model. |
| Search a long set's ids in a sorted copy instead of scanning them | TLCSailfish1 | 4.15, 4.41, 3.88 s → 4.16, 4.38, 3.83 s | Its sets are new in most states, so each copy is sorted for few tests. |
| Read a key's metadata only where a short domain doesn't hold its id | MCabs | 12.22, 11.21 s → 11.68, 11.48 s | The misses are on the function's own words, which are read either way. |
| Share one parse between SANY's report and the lowering | 2PCwithBTM, TCommit, TwoPhase, DieHard (`-workers 1`) | Not built: tokenizing and parsing a spec and its standard modules takes 0.26–0.66 ms of 7.9–16.7 ms runs, 3–5% at most | The report's resolution, level checks and linting stay, and the run goes to lowering (25–33%), the process (about 2 ms) and the engine's setup; such a run is already far below TLC's startup. |
| Read the operands of arithmetic, comparisons and other binary and unary builtins in place (`predicate::Leaf`) rather than through their closures | BufferedRandomAccessFile, MCabs, MCMultiNode, PaxosCommit | 1.66 → 1.59 s, 10.29 → 10.27 s, 5.71 → 5.66 s, 17.9 → 18.6 s | An indirect call to a leaf costs a nanosecond or two; see below. |
| Intern the integers to 65,535 at reset rather than to 4,096 | BufferedRandomAccessFile | 1.60 → 1.62 s; 2PCwithBTM's start-up 14 → 21 ms | `store.int`'s share is the small integers' own path, not the hash table. |
| Intern a tuple in place | cf1s_folklore | Not built | `tuple_of` already hashes the stack in place and copies only a new tuple; 69% of `intern_block` is the first load of the intern table's slot, a cache miss. |

**Evaluator dispatch, bounded.** An instrumentation build counted every evaluation of a compiled
closure (`eval`, by the place that made it), at one worker: 256M in BufferedRandomAccessFile's
1.60 s, 2.05G in MCabs' 10.2 s, 376M in MCMultiNode's 5.7 s and 861M in PaxosCommit's 18.5 s, 5 to
21 ns each with all their work. Leaves that only return a value (a constant, a variable, a bound
name, a value computed once) are 42%, 33%, 10% and 57% of them. Samples whose instruction lies in
the calls themselves (the `Arc` deref, `?`, the `Fn` shims) are 8–16% of the profiles. A flat
register form or fused super-nodes would remove at most that, about 1.1–1.15×, and the operands read
in place above, its cheapest slice, measured 0–4%. The rest of the closures' time is the store's,
the memo tables' and the state table's memory, which their own tracks address.

Counts behind the quantifier index, from an instrumentation build that counted every quantifier,
set filter or action-level `\E` whose body starts with `m.f = e` on the bound name:
- PaxosCommit (17.0M states generated): about 178M element visits, of which about 140M fail the
  leading test.
- FastPaxos: 6.3M visits.
- MCMultiNode and cf1s_folklore: no site of this shape.

### Fingerprints and the state table

| Idea | Model | Result | Why it lost |
|---|---|---|---|
| Fingerprint a successor whose values change length by independent terms: the parent's prefix before the first changed value shifted by the successor's length from there, each value's F shifted by its tail up to the last changed value, and the parent's terms after it, with each value caching its last term (the same 64-bit value) | MCbtree, MCExactInitialSync | Cachegrind against main: MCbtree 12.17B → 11.90B instructions and 152M → 46M L1 data misses; MCExactInitialSync 163.7B → 169.7B instructions and 3.98B → 2.99B L1 data misses. Wall at 1 worker: MCbtree 1.77 → 1.52 s (11 runs), MCExactInitialSync 31.2 → 34.0 s (5 runs) | 88% of MCbtree's and 65% of MCExactInitialSync's successors change a value's length, and the old path re-extends from the first changed value. On MCExactInitialSync the changed span is nearly as long (6.8 of 9 values), so the terms' table lookups and cache writes cost what the shorter chain saves. 59% of its terms hit the cache. Not kept. |
| Shift fingerprints by 4-bit tables (2 KB a length) instead of 8-bit ones (16 KB), the same values | MCbtree, MCExactInitialSync | Cachegrind on MCbtree: 12.41B → 13.37B instructions, 144M → 106M L1 data misses. Wall: MCbtree 1.61 → 1.53 s (11 runs), MCExactInitialSync 25.88 → 27.21 s (5 runs), both within noise | The tables' misses are served from L2 and the last level, not memory, so halving the misses buys less than the 16 loads a shift then takes cost. A carry-less multiply (speed.md) trades the same way: its dependent chain is about as long as an L2 hit. |

**State storage, designed and not built.** A compact store would code each variable's ids by a
dictionary per variable. It gains no time and saves memory only on models whose state store
dominates their memory. Measured on main 9bf3b18, one worker:

| Model | States, variables | Stored ids | Parents, fingerprints, seen-set | Peak RSS | Distinct ids per variable |
|---|---|---:|---:|---:|---|
| MCExactInitialSync | 9,610,407, 12 | 461 MB (48 B a state) | 38, 77, 268 MB | 901 MB | 27, 2935, 6993, 4, 12, 4, 5, 4, 11, 27, 1, 160 (61 bits a state) |
| PaxosCommit | 1,321,761, 3 | 16 MB | 5, 11, 34 MB | 719 MB | 12, 55696, 888713 (40 bits) |

- **Time:** what a compact store removes is about 4.5% of MCExactInitialSync's self time and 2%
  of PaxosCommit's, at most 1.05× and 1.02× before encoding and decoding. That covers copies, the
  states' pushes, `realloc` and page faults.
- **Memory:** a 16-bit code per variable takes MCExactInitialSync's stored ids from 461 to
  231 MB, about 25% of its peak. Packed codes (8 B a state) take them to 77 MB, about 43%.
  PaxosCommit's memory is its value store, so it saves 2–3%.
- **Design:** each variable keeps an id → code map to encode and a code → id array to decode.
  The expanded state is decoded once per parent. Traces, liveness, state logs, checkpoints and the
  threads' merge read states through `States::state`, which would decode.
  - A variable whose dictionary outgrows its width needs the store re-packed, or a 16- or 32-bit
    code chosen per variable as it grows (the −25% figure).
  - Output is unaffected.

### Memo tables and the memory layout (`perf-memo`)

What the memo track built, measured and dropped, and why the store's memory layout stays as it is.

**Built:**
- #179 clusters a large table's entries by its first key.
- #187 shares a table's room between a search's threads.
- #193 passes the elements a loop's leading `x.f = c` rejects.
- #201 turns off a full table that misses more than it hits, and unites a set with one element by a binary search.

**Measured and dropped:**

| Idea | Model | Result | Why it lost |
|---|---|---|---|
| Huge pages on every allocation of 4 MiB or more (a global allocator) | the suite at 232aa8d + #179 | PaxosCommit 1.07×, MCMultiNode 1.05×; MCbtree, Detlefs, GameOfLife, SpanTreeRandom 0.94–0.95×; geomean 1.00× | Faulting and zeroing 2 MB pages costs the short runs what the long ones gain. |
| A memo per action, keyed by the variables the action reads | PaxosCommit, MCMultiNode | Not built. `msgs` is new in 848K of PaxosCommit's 1.2M expansions, so at most about 30% would hit. MCMultiNode's work keyed on `history` is already in tables that hit 92%. | The ceiling is about 15% of PaxosCommit, before replaying successors costs anything. |
| Prefetch each large table's run when a state becomes current | MCMultiNode | 5% slower | Most tables aren't read for a given state. |
| Take a table's home from the hash's high bits, so that growing writes in order | MCLamportMutex, MCMultiNode, PaxosCommit | No change over 5 interleaved runs of each | The rehash reads sequentially, and hardware prefetch hides that. |
| A total memo budget per thread instead of a cap per table | PaxosCommit and MCMultiNode at 4 workers | At 2^22 entries: PaxosCommit 12.90 → 14.27 s (1421 → 855 MB); MCMultiNode 3.47 → 3.57 s (935 → 599 MB) | The tables that fill first take the room PaxosCommit's hot tables need. |
| A cache from (set, element) to the id of their union | PaxosCommit | Not built. 13.0M single-element unions over 9.09M distinct pairs. | Only 30% recur, and the cache would itself miss memory. |
| A size cap without eviction, at 2^12–2^20 entries; clustering in bands of 8 or 64 slots | MCMultiNode, PaxosCommit | Slower at every cap and band | The caching pays even at a miss to memory, and a band spreads a state's run. |

**Where the misses are.** These are cachegrind runs, because this container exposes no hardware counters (`perf stat` reports them as not supported). Each is a full one-worker run at #201's head, simulating a 32 KB D1 and a last level of either 2 MB (standing in for L2) or 32 MB (standing in for memory). Misses are data-read misses, attributed by function and grouped:

| Group | MCLamportMutex, 2 MB | MCMultiNode, 2 MB | PaxosCommit, 2 MB | MCLamportMutex, 32 MB | MCMultiNode, 32 MB | PaxosCommit, 32 MB |
|---|---:|---:|---:|---:|---:|---:|
| All data-read misses | 13.4M | 25.3M | 39.8M | 3.2M | 15.7M | 3.4M |
| Memo rows (`memo_lookup`, `set`) | 31.7% | 26.1% | 23.2% | 28.2% | 28.4% | 23.6% |
| Intern table probe (`intern_block`, `intern_patched`) | 12.2% | 6.7% | 12.6% | 8.8% | 4.4% | 7.5% |
| State table (`States::find`) | 8.1% | 7.5% | 9.2% | 11.9% | 6.7% | 3.8% |
| Fingerprints (`get_child`, `shift_by_table`) | 13.7% | 5.3% | 9.3% | 9.4% | 3.5% | 5.7% |
| Store metadata and heap words (apply, fields, compare, `find_in_block`) | 7.2% | 1.2% | 4.4% | 2.2% | 1.2% | 3.3% |
| Sequential: memo rehash | 7.4% | 31.6% | 17.4% | 9.7% | 37.8% | 32.1% |
| Sequential: `memcpy`, state-table growth, allocation | 13.1% | 14.1% | 18.6% | 27.5% | 13.9% | 20.9% |

Cachegrind has no prefetcher, so it overcounts the sequential groups. Taking the home slot from the hash's high bits, so that the rehash writes in order, confirmed this: wall time didn't move.

**The bound.** Pricing a miss at about 40 cycles to L3 and about 200 to memory:
- All random-access stalls are 15–20% of MCLamportMutex, and under 10% of PaxosCommit and MCMultiNode. So no store or memo layout is worth more than about 1.1–1.2× at one thread.
- The candidates on their own come to less:

| Candidate | Ceiling |
|---|---|
| Memo rows next to their key's value | 5–8% on MCLamportMutex and MCMultiNode, about 4% on PaxosCommit |
| A tag array in front of the intern table | about 3% |
| Store metadata split by kind, a state's values contiguous, or a composite's header beside its block | 1–2% (the membership session bounds the last at ≤1.05× on MCabs) |
| Immediate integers | ≤4% on BufferedRandomAccessFile; the test on every metadata read cost 11–15% in compare-heavy code (the lead's experiment) |
| A nursery for recent values | only 5–15% of metadata loads hit values interned in the last 2^16 (track 6) |
| Huge pages on the intern table alone | no change (track 6) |

**Threads.** Four independent one-worker runs of the same model at once each take 0–4% longer than one run alone on the 4-core container:

| Model | One alone, s | Each of four at once, s |
|---|---|---|
| PaxosCommit | 21.2–21.9 | 22.1–22.4 |
| MCMultiNode | 6.7–6.8 | 6.7–7.0 |
| cf1s_folklore | 20.0–20.6 | 20.0–20.3 |
| MCLamportMutex | 3.4–3.5 | 3.5–3.6 |

So shared caches and memory bandwidth don't explain the threaded search's extra CPU either. The same experiment with 16 runs on the 16-core runner would bound it there.

**L1.** `Fingerprints::shift_by_table` causes 27.5% of all D1 misses on PaxosCommit and 36.9% on MCLamportMutex. Each length has its own 16 KB table, and those tables cycle through a 32 KB L1. The fingerprint session measured both fixes:
- 4-bit tables cut L1d misses by 27% but add 7.8% instructions, with no gain in wall time.
- A carry-less multiply is bounded at about 20 cycles of dependent chain, against about 14 for the loads.

Neither was built.

## Startup constants and the memo at any thread count

EWD998ChanID_shiviz (7 nodes) reached Progress(5) quickly on 1–3 threads, but seemed to stall on 4.
Two engine costs grew with the number of threads, and a shared level reported no progress until it ended. None of this holds any more.

**Constants.**
- TLC evaluates each constant-level definition of arity 0 once, at startup, and every worker reads that value (`SpecProcessor.processSpec`, SpecProcessor.java:202–207; `processConstantDefns`, 226–233 and 343–381; `evalConstantDefn` normalizes the value because "All workers share the value", 237–242).
- The engine evaluates a pure definition of arity 0, such as RingOfNodes (a CHOOSE over 7^7 functions), on its first use and keeps the value in the machine's `onces`. Each worker started with none of them, so each chose RingOfNodes again.
- And a value the store didn't hold was dropped by the worker's overlay at each level, so it was evaluated again at every level.
- Now a worker takes the values the search's machine computed each time it lays its overlay. After a level, the search's machine imports the values the workers computed and it lacks.
- A value computed once reads no state, and sharing is off wherever an evaluation could differ between threads: lazy functions, TLCCache, ToString's ranking, Print and the random draws. So each thread that computes one computes the same value, and which thread's is imported shows nowhere.

**Recursive definitions.**
- TLC doesn't cache the applications of a recursive function. A LET makes the function once per evaluation of the LET (`LazyValue`, Tool.java:1849–1860; `OPCODE_rfs`, 2354–2380), and `FcnLambdaValue.apply` evaluates the body anew each time (FcnLambdaValue.java:153–263).
- So Utils' `IsSimpleCycle`, which reads `F[i-1]` twice, costs TLC 2^n − 1 bodies a call. The engine's memo table makes that n.
- But each table took at most 2^22 / threads entries, refused more once full, and turned itself off when under half the lookups of a window then hit.
- On 4 threads, F's table (keyed by the candidate and i) filled at 1,048,576 entries while RingOfNodes was being chosen. Every later call then missed, and the choice went from linear to exponential. On 3 threads the choice ended before the table filled.
- Now the table of a recursive operator or function is kept (`MemoTable::kept`): it doesn't turn off once full, and when full it forgets what it holds and goes on. Entries for earlier candidates are dead anyway, so each call keeps its hits within any room that holds one call's entries. Memory stays as before.
- Its probation stands: a table under 20% hits in its first 8,192 lookups turns off, which those lookups decide on any number of threads. Without it, GameOfLife's recursive definition, whose table rarely hits, took 2.95 s and 224 MB on one thread against 1.22 s and 47 MB. A recursion that reads a call twice hits about half the time, and keeps its table.
- A value in a memo table is a function of its keys, and an evaluation that fails stores nothing, so clearing a table changes no value and no decline.

**Progress.**
- TLC's workers share one queue and never wait for a depth to end. Its main thread starts them, waits up to 3 s (AbstractChecker.java:451), then loops: `doPeriodicWork` and `runTLCContinueDoing` (AbstractChecker.java:466–488), which prints `printProgresStats` (ModelChecker.java:1013, 940–959) and waits `progressInterval` (ModelChecker.java:1035), 60 s by default (TLCGlobals.java:221–222).
- So its first report comes about 3 s in and then every 60 s, at whatever depth the workers are.
- The engine's one thread checks the clock every 256 states on that schedule. A shared level reported only at its end, so EWD998ChanID_shiviz's level of 860K states printed nothing for as long as it took.
- Now the search's thread, while a shared level runs, waits for the threads or the next report, whichever comes first, and reports from counts each thread keeps of the level:
  - states generated: before the level, plus each thread's;
  - distinct: before the level, plus the most new states any one thread found, a count the merge can only exceed, so it never drops;
  - left on the queue: distinct less the states expanded.
- The timer only wakes the thread to report; it stops nothing. A periodic check of the temporal properties, which TLC makes with its report, still waits for the level's end, and the one-thread search is unchanged.
- The relay flushes what it printed whenever the search has nothing more to say, as TLC prints each line as it goes, rather than at the first report.
- PROVE_IT_TEST_PROGRESS_AT names a state: the thread that claims it waits until the search's thread has reported, so a test sees a report inside the level without a clock.

**Tests.**
- Two hooks bound the tests by work, not time, beside PROVE_IT_TEST_PROGRESS_AT:
  - PROVE_IT_TEST_MEMO_ENTRIES sets the room the tables share.
  - PROVE_IT_TEST_EVALUATIONS sets how many bodies of recursive definitions a search's machines may evaluate before it stops.
- The tests in `prove-it-check`'s `check.rs` use the ewd998 example's IsSimpleCycle and RingOfNodes, and fail on the code before this change.

## Designs ready, not built

### Pruning `x' \in [S -> T]` by per-key constraints (MCabs)

MCabs enumerates `cLogs' \in [Servers -> Seq(Terms)]`: 64,000 candidate functions per
enumeration, filtered by `IsPrefix(cLogs[i], cLogs'[i])` and
`\A j \in Servers \ {i} : cLogs'[j] = cLogs[j]`. Pruning to the candidates the per-key constraint
admits would turn 64,000 into about 40.

**TLC's order** (tlaplus d8fb231):
- `Tool#getNextStates`, `OPCODE_in` on a primed variable (`Tool.java:1422-1466`), evaluates the
  right side once. For each element of `Enumerable.elements()` it binds `x'` and evaluates the rest
  of the conjunction, left to right. A FALSE guard abandons the candidate; an error aborts the run
  at that candidate.
- `SetOfFcnsValue.Enumerator` (and `DomIVEnumerator` for an interval domain) is an odometer over
  the domain sorted by TLC's order. The last key varies fastest, and each key's values come in T's
  order.
- Under `-coverage` it counts `cm.incSecondary(|S|)` per candidate.

**The shape.** `x' \in [S -> T] /\ C1 /\ … /\ Ck /\ …`, where Ck is a per-key constraint,
`x'[a] = e` or `\A j \in D : x'[j] = e(j)`, with D and e not mentioning x'. The survivors are the
candidates with f[j] = e(j) for every constrained j.

**When skipping is exact.** Every skipped candidate must evaluate to FALSE at some conjunct up to
Ck, without an error or an effect. C1 … C(k-1) must be free of effects, and must read x' only as
x'[b] for keys b that Ck leaves free.

Errors are positional: TLC raises at the first candidate in its order whose chain errors, which may
be a skipped candidate that comes before every survivor. To stay exact, run a pre-pass per state:
- Evaluate C1 … C(k-1) once for each combination of values of the free keys: |T| evaluations for
  one free key, 40 on MCabs.
- Evaluate Ck's targets e(j), and check each one's equality with every element of T.
- If nothing errors, skipping is exact. If anything errors, enumerate in full, as today.

D must be a subset of S; otherwise fall back.

**What stays the same.** With the constrained keys fixed, the odometer visits the survivors in the
order of the free keys' values. Successor order, state numbering, traces, and any later Print or
error therefore stay TLC's. The states-generated and distinct counts count successors only, so
they are unchanged. Under `-coverage`, don't prune.

**Why it isn't built.** A grep of the corpus, tlaplus/Examples included, finds the shape in an
action only in MCabs (`ccf/tla/consensus/abs.tla`). Every other `x' \in [S -> T]` is a TypeOK' in a
`*_proof.tla` or a TLC test model. The 18 `\E f \in [S -> T]` outside proofs are in Init, in
invariants or ASSUMEs, or constrain the whole function. Build it only if axiomatic actions
(`x' \in TypeSet /\ constraints`) turn out to matter beyond the suite.

**Reach, measured.** An instrumentation build counted each element an action's `x' \in S`
enumerates (S of more than one element, outside Init), over the whole-corpus differential (664
models within its 20 s cap) and the suite. MCabs enumerates 137,472,000 functions for 5,819
successors. No other model enumerates more than 13,824 (TLC's `coverage/M`, then
`RandomSubsetNextTuples` with 8,186 and `Github648` with 1,512), all of them already fast. Built,
it would take MCabs from 10.2 s toward start-up, and so the suite's geomean by about 1.3×, from one
spec's idiom.

Tests to write if it is built: an error at the first, a middle and the last block of the odometer,
compared with TLC.

### Answering liveness action atoms from the steps the search took

On cf1s_folklore, `answer_atoms` is about 12.5 s of about 21 s at one worker. Most of it, about
11.4 s, is one action atom, `<<A>>_vars` of `WF_vars(\E self \in Proc : Receive(self) \/
Propose(self) \/ Decide(self))`, evaluated as a predicate on each of 22.4M steps. SpanTreeRandom
has the same shape.

**Ceiling.** A prototype on main ad7ca16, 1 worker, reduced each step's answer to the subscript
test, without evaluating A:

| Model | Now | Prototype | Ceiling |
|---|---|---|---|
| cf1s_folklore | 18.5 / 19.3 s | 10.1 / 10.6 s | about 1.8× |
| SpanTreeRandom (`WF_vars(Next)`) | 2.9 / 3.5 s | 0.8 / 0.8 s | about 4× |
| StarkMutex (`benchmarks/liveness`) | 7.3 / 7.9 s | 6.0 / 6.5 s | about 1.2× |

**TLC** (d8fb231):
- `ModelChecker` runs `oos.checkAction(tool, s0, s1, …)` on every successor in `nextStates`
  (`LiveCheck.java:121-128`). `nextStates` holds the in-model successors (after CONSTRAINT and
  ACTION_CONSTRAINT), one per fingerprint. The checks run on the actual successor, not on the
  symmetric representative.
- `LNAction#eval` (`LNAction.java:66-85`) evaluates the subscript in both states first. If they are
  equal, `<<A>>_v` is FALSE (and `[A]_v` TRUE) without evaluating A. Otherwise it evaluates A as a
  boolean with both states bound, `Tool.eval(body, con, s1, s2)`: predicate mode.
- Generation (`Tool#getNextStates`) walks the disjuncts and `\E`s:
  - `x' = e` assigns when x' is unbound and tests otherwise;
  - `x' \in S` enumerates S;
  - UNCHANGED assigns.
- `Tool#getActions` (`Tool.java:269-417`) splits Next for TLC's actions only at `\E` over an
  enumerable set (`OPCODE_be`) and at disjunctions (`OPCODE_dl`, `OPCODE_lor`), through operator
  applications. Anything else is one action, a conjunction list (`OPCODE_cl`) included.

**Findings.**
1. **The native front end matches no atom onto TLC's split.** `tla-front` lowers every ENABLED atom
   with `EnabledActions::Unknown` and `is_labelled: false` (`lower.rs`). Only the deleted
   TypeScript checker did the matching (`findActionPositions` in `spec-description.ts`, gated by
   `!isConstrained && !hasRepeatedEffects` in `check.ts`). Branch `atom-actions` ports it into
   `tla_trace::add_actions`:
   - each atom's action is split with the same `Splitter` as Next;
   - pieces are matched in order by node, and by scope chain with `is_same` bound values;
   - ENABLED positions are filled in where there is no CONSTRAINT and no Print, PrintT, TLCSet,
     TLCGet or JavaTime;
   - `is_labelled` is set where some ENABLED atom needs a proper subset.

   On SpanTreeRandom, ENABLED of `WF_vars(Next)` then maps to all of Next and is answered from
   steps, but the time does not move: ENABLED is not the cost. So it was not opened as a PR alone.
2. **cf1s's Next is one TLC action.** It is `/\ \E self \in Proc : …`, a one-item conjunction list,
   which `getActions` does not split. Labels by TLC action carry no information there. cf1s needs
   the engine's own finer labels: plan (ii).
3. **The error guard needs the walker.** Predicate mode differs from generation only in three
   comparisons:
   - `x' = e` becomes equality of t[x] with e;
   - `x' \in S` becomes membership of t[x] in S;
   - `UNCHANGED x` becomes t[x] = s[x].

   Every other read of x' happens only after x' has compared equal to the value generation assigned
   on that branch. Generation would have failed on a read before an assignment, and a membership
   that holds means generation enumerated that element. TLC's `equals` and `member` can raise across
   kinds: IntValue with a string, typed model values, records against functions, unranked strings.

   The operands of those comparisons need not appear in any recorded state: a disjunct can assign
   `x' = e` and then fail a later conjunct. So the guard must join the shape (the comparability
   classes of #168 and #176) of every value the walker assigns to a primed variable, in Init and in
   every successor, kept or not. The sites:
   - `Op::Assign` in `Segment::apply`;
   - `either_step`;
   - the membership enumeration (`walk_memberships`);
   - Init's assignments.

   If every variable's joined shape is safe, no comparison can raise.

**The claim.** Let A split, by the same split as the steps' labels, into a subset of Next's pieces.
Then for a recorded step s→t, A(s,t) is TRUE iff some recorded step s→t carries a label in A's set.
Why:
- On the fragment generation handles without error, generation produces exactly
  {t : D(s,t)} for each piece D.
- The split is logically the disjunction.
- t is recorded only when in the model, which is the only case where TLC checks it.

Predicate mode stops at the first TRUE piece, which changes nothing when nothing can raise. Where
several steps s→t carry different labels, the answer is TRUE if any label is in the set.

**Plan (i): an atom whose action is all of Next** (SpanTreeRandom's `WF_vars(Next)`). Every recorded
step is a step of A, so `<<A>>_v` is the subscript test alone, with no labels at all. Needs the
walker-hook shape guard and the fallbacks below.

**Plan (i), as built.**
- `compile_atom` marks an action atom `is_next` where its expression is the next-state relation:
  the same node, or the same global definition named with no arguments, in the same scope. Its
  compiled footprint must read nothing of the search (TLCGet, the registers, prints and draws), and
  `Compiler::is_walk_repeatable` must find no ENABLED, `\cdot`, `[A]_v`, `<<A>>_v`, temporal
  operator, subexpression selector, or JavaTime, TLCModelValue, TLCDefer, Trace or JSON builtin
  through the definitions it names. It doesn't look into the constant definitions TLC computes as
  it starts (`NORMALIZED`), such as SpanTreeRandom's `Edges`, which draws.
- Where an atom is marked, the machine keeps a `ShapeJoin` per variable (`Machine::assigned_shapes`,
  on #176's shapes), and the walker joins every value it assigns: `Op::Assign`, `either_step` and
  the membership enumeration, in Init and Next. Each search thread joins in its own overlay, and the
  level's merge imports the values that widened a thread's joins into the store and joins them
  there. Unmarked runs pay one branch on a `None` per assignment.
- A membership `x' \in S` joins only the elements the walk enumerates, but TLC's predicate
  evaluation tests `t[x]` against S itself, through S's `member`. Three Codex findings on #197 were
  sets whose `member` fails where the walk joined nothing: an empty `[a : {}]`, which still checks
  the kind; `[a : {}] \cup {1}` and `SUBSET [a : {}]`, which hold such a part; and
  `x' \subseteq [a : {}]`. So the guard is a whitelist (`is_membership_covered`), each form from its
  `member` at d8fb231, and every other set turns the shortcut off (`Machine::is_membership_unsafe`):
  - an enumerated set: `SetEnumValue.member` is `ValueVec.search`, which compares `t[x]` with the
    elements by `compareTo` (sorted) or `equals`. The walk assigned each element, so the join
    covers each comparison; an empty one compares nothing;
  - an integer interval: `IntervalValue.member` takes an integer, and fails otherwise only where
    the interval isn't empty and `t[x]` isn't an untyped model value; the walk assigned an integer
    from it, so a comparable join is integers and untyped model values;
  - a definition with no arguments, which is the set its body is.

  Records, functions, products, SUBSET, unions, UNION, filters, maps, constants, Nat and the rest
  go back on only with a citation of their `member`, the argument for an empty part, and the grid
  below. A walk of Next that enumerates an empty set, or assigns by `x' \subseteq S`, also turns
  it off. Init's memberships don't (cf1s's `pc \in [Proc -> {"V0", "V1"}]`): `LNAction.eval`
  (`LNAction.java:66-85`) evaluates the atom's action body alone, which for `WF_v(Next)` is Next,
  so the memberships predicate mode tests are nodes of Next, reached, by the induction above, on
  a path a walk of Next took, and that walk turns the shortcut off where it enumerates one the
  guard doesn't cover. Init's walk is of the initial predicate, which TLC doesn't evaluate there;
  where Next names Init, its walk of Next walks those nodes too. Init's values are still joined,
  which UNCHANGED compares. The grid has 22 cells for it: Init assigns from each of the eleven
  forms, with a part empty and not, and Next assigns values of that kind.
  The grid, `prove-it-cli/tests/membership-grid`, has 396 specs: x' \in S beside two other
  assignments, under WF_x(Next) (answered from the steps where the guard lets it) and
  WF_x(Alias) with Alias == Next (evaluated). S is each of eleven forms, with a part empty and not,
  in seven nestings, and the other assignments are integers, values of S's kind, or integers in
  the nesting's shape. Both formulations must print the same and match TLC's output at d8fb231, at
  1 and 4 workers. The PR's first head fails it on 102 runs, the head after the union fix on 6.
- `LiveGraph::is_next_taken` holds where no walk took the shortcut (`is_enabled_exact`), no string
  was ranked since the order froze (which can take a string out of its class after its shape was
  joined), and every variable's join is comparable. TLC's `equals` fails only where `compareTo`
  does, for these classes: an untyped model value is never equal to another kind
  (`modelValueEquals`), and a typed one fails against other kinds in both.
- `answer_atoms` answers a marked atom on a step the search took with 1 once the subscript test
  finds the subscript changed, on both the helpers' path and the one-thread path; the stuttering
  steps and everything else are evaluated as before. PROVE_IT_LIVE_CHECK evaluates the action too
  and stops with `NEXT_DIFFERS` where it doesn't hold.
- SYMMETRY and VIEW need no fallback: the graph's steps are then the real successors (`Reals`),
  which the walk generated, and expanding the states past the stored ones walks Next too.

**Plan (ii): the soundness argument.** Write Next's walk from a state s as a tree, in TLC's
order: a node chooses a disjunct, a value of an `\E` or of `x' \in S`, or goes on to the next
conjunct. A path π assigns the primed variables, σ(π), and ends in t(π) where it assigns them all.
A *piece* is a node n of that tree reached under bound values ρ; its *context* C(n, ρ) is everything
on the path from the root to n, and after it to the end of every conjunction n is inside: the
conjuncts before n's ancestors, those after them (a later guard can reject t), and the choices of
disjuncts and values that lead there.

*Matching.* An atom's action A matches a set P of pieces when A ≡ ∨_{(n,ρ)∈P} (C(n, ρ) ∧ n[ρ]),
read off the two trees side by side:
- through a disjunction or an `\E`, A may take a subset of Next's disjuncts, or of the values of a
  bound whose set has the same value in both (the same constant, such as cf1s's `Proc`);
- through a conjunction only where it is the same node in both, or a list of one item, which is
  that item (cf1s's `Next == /\ \E self \in Proc : ...`);
- through an operator application only where both apply the same global definition to argument
  values that are equal under ρ (the same bound name, or the same constant), so that the bodies
  are the same expression in equal contexts. A LET-bound operator, an operator argument (a
  higher-order parameter), an INSTANCE with substitutions or a definition of another module falls
  back unless it is the same node under the same bindings.
Everything else, a piece whose context A lacks above all, does not match, and the atom is
evaluated as today.

*Why the context is needed.* With `Next == (G /\ A) \/ B`, G false at s and A(s, t) true for a t
that B generates, TLC evaluates `<<A>>_v` standalone and gets TRUE, but no path through A generated
t. Splitting through conjunctions without the context, as this section first planned, is wrong.

*Labels.* Each step the graph keeps (in the model: past CONSTRAINT and ACTION_CONSTRAINT, as TLC
evaluates atoms only there) carries one bit per matched atom: whether a path that generated it
passed through a piece of P. The bits of every path that generates the same s→t are ORed, a path
that finds t already seen included.

*Claim.* For a step s→t the graph keeps, `A(s, t)` is TRUE in TLC's predicate evaluation, without
failing, iff the step's bit is set, where plan (i)'s guard holds.

(⇐) A path through (n, ρ) ∈ P is a conjunction of every guard and assignment on it, which includes
C(n, ρ) ∧ n[ρ]; it holds of (s, t(π)), so A does, and by (⇒)'s induction its evaluation can't fail.

(⇒) By induction over TLC's predicate evaluation of A on (s, t), stated for any expression e that
A's evaluation reaches under bindings ρ: *when the evaluation reaches e, every conjunct before it
held of (s, t), and there is a path of the walk from s that reaches e's node under ρ with
σ ⊆ t: it assigned every primed variable it assigned so far as t has it.* At the root, the empty
path. Then by the form of e:
- `x' = e1` with x unassigned in σ: the walk evaluates e1 under the same s, ρ and σ, so to the
  same value, without failing (the search completed), and assigns it; the predicate compares
  t[x] with it. Where they are equal, σ ∪ {x ↦ t[x]} ⊆ t extends the path. With x assigned, both
  compare the same two values.
- `x' \in S`: the walk enumerates S, every element (it is exhaustive), so where t[x] ∈ S a branch
  assigns t[x]. Where S is a set TLC keeps lazy, the predicate's membership test runs only what
  the enumeration ran (a filter's predicate on an element of S, which the enumeration evaluated
  on every element).
- `UNCHANGED x`: as `x' = x`.
- a guard: every primed variable it reads is in σ (the walk would fail reading one that isn't,
  and the search completed), so it has the same value as on the path.
- `e1 /\ e2`: in order; e2 is reached only where e1 held, and the path through e1 extends σ.
- `e1 \/ e2`: the predicate stops at the first TRUE disjunct; the walk takes both. The walk
  evaluates a superset, so each disjunct the predicate reaches is reached by a path with the same σ.
- `\E y \in S : e1`: S has the same value; the predicate stops at the first TRUE value, the walk
  takes every value, again a superset.
- `IF`, `CASE`, `LET` and an operator application: the walk evaluates the condition, the arms in
  order, the definitions and the body as the predicate does, with the same values.
So every expression the predicate evaluates the walk evaluated with the same values, except the
three comparisons, which plan (i)'s guard covers: the predicate can't fail where the walk didn't.
And where A(s, t) is TRUE it is TRUE through some (n, ρ) ∈ P: the path the induction carries to
the end of C(n, ρ) ∧ n[ρ] has σ = t, so it generated t, and its bit is set.

The induction needs the walk not to shortcut (`is_enabled_exact`), and fails, so the atom falls
back, where a piece holds: a primed variable read before the walk assigns it in a form the
predicate evaluates but the walk can't (a primed operator application `(A)'`, ENABLED, `\cdot`,
`[B]_w`, `<<B>>_w`), a value the walk keeps lazy and the predicate reads otherwise, or anything
plan (i) falls back on.

*Stuttering.* A path that generates t = s sets the bit of that step, but the subscript test
comes first and answers it: `<<A>>_v` is FALSE of a step that leaves v unchanged. The stuttering
slot each state has for the checker is evaluated as today.

*Where it falls back:* every case plan (i) falls back on; a piece whose context A lacks; `\E` sets
that aren't the same constant; operator arguments not shown equal; VIEW and SYMMETRY to begin with,
where the steps are rebuilt as real successors and the bits would have to follow them.

*Layout.* One bit per matched atom per step, in a `Vec` pushed next to `labels` in
`check_complete_successor` and copied in `expand_level`'s merge over the same `steps` range (the
liveness climber's layout after #184), kept only where an atom is matched.

*Tests against TLC at d8fb231:* cf1s's shape (a one-item conjunction around `\E` and disjuncts);
WF over a subset of the disjuncts under each bound value; a later guard in Next's conjunction that
rejects a successor the atom's piece alone allows (must fall back, and print what TLC prints);
`Next == (G /\ A) \/ B` with WF_v(A) (falls back); an operator applied to equal and to different
arguments; a successor two pieces generate, one inside A and one outside, and one already seen;
a type-mixed piece where TLC's predicate fails; WF over an action with a stuttering path; a
CONSTRAINT that discards a target; at one and four workers.

*What the walk joins.* The membership enumeration joins the shape of every element it tries,
including those a later conjunct rejects, and `t[x]` was itself assigned by some walk, so its shape
is in the join too. TLC's structural memberships (`[A -> B]`, `SUBSET S`, record sets) compare
`t[x]` with values of that join; Nat, Int and `Seq(S)` the walk can't enumerate at all.

*"The search completed."* The tables answer only steps from states whose expansion finished
without error: every step the graph records, also where the liveness checker runs before the
search ends. That is what the induction leans on when it says the walk evaluated an expression
without failing.

**Plan (ii), as built.**
- `Compiler::add_pieces` (`compile/pieces.rs`) reads the atom's action and Next side by side as
  above. Two expressions are the same where they are the same node outside any bound name, the
  same number or string, or the same global operator, builtin, constant or variable applied to
  arguments that are the same, a bound name standing for the one of Next's it was paired with.
  An `\E` pairs its names only over the same constant (a declared one, or one TLC computes as it
  starts). A disjunct of Next is tried as it stands before either side's definition is unwrapped,
  so `WF_x(A)` over a disjunct `A` of Next matches it. The matcher asks for no other conjunct beside a piece, though a conjunct at the top of
  Next holds of every step the search keeps, so it couldn't change an answer; context inside a
  disjunct or under a bound value can, which `(G /\ A) \/ B` tests.
- `EngineContext::build` matches each action atom before it compiles Next (at most 64, a bit
  each), and the walker wraps the walk of each matched node so that it sets the atom's bit on
  `Machine::piece_bits` while it runs. The pipelined search checks a successor one step later,
  so the bits wait with it (`pending_pieces`). Once Next is compiled, an atom keeps its bit only
  where the walk went through each of its pieces (`Compiler::is_piece_walked`): a piece the
  compiled walk never wraps would leave the bit unset on steps A holds of.
- `Graph::pieces` keeps `piece_width` bytes per step, (n + 7) / 8 for n answered atoms, next to
  `labels`, and the threads' merge copies them over the same steps, only where an atom is matched
  and there is no VIEW or SYMMETRY. A run with no matched atom keeps nothing per step.
- `answer_atoms` answers such an atom on a step whose subscript changed with whether any step from
  the same state to the same successor has the bit, under plan (i)'s guard, on both paths.

**Plan (ii) from TLC's actions.** Where the search labels its steps with TLC's actions (some
ENABLED atom splits into some of them, `tla_trace::add_actions`), the pieces are off, and an action
atom of a fairness answers from the labels, as "The claim" above first planned. TLC builds the
action and the ENABLED of `WF_e(A)` and `SF_e(A)` from the same body and context
(`new LNStateEnabled(body, con, subs, false)` and `new LNAction(body, con, subs, false)`,
`Liveness.java:497-514`), so the positions `find_enabled_actions` found for the ENABLED are A's
split into TLC's actions: each the same expression in an equal scope as one of Next's
(`getActions`, `Tool.java:273-410`: disjunctions, `\E` over sets evaluated as TLC starts, operator
applications with their arguments' values bound, LET and labels). `get_split` takes them where
the ENABLED atom is `<<A>>_v` of the same node in the same scope; `Taken::of` answers every step
where they are all of TLC's actions (A ≡ Next, as plan (i)), and otherwise whether some step from
the state to the successor has one of their labels. The labelled search walks each of TLC's actions
exhaustively, so the claim's induction holds of each split action as of a piece, under plan (i)'s
guard, with A reading nothing of the search and passing `is_walk_repeatable`. Where the search
couldn't compile TLC's actions it walks Next unlabelled, and the atom is evaluated. StarkMutex runs
this way: each of its 45 atoms answers from the labels of its process's action.

**Plan (ii) under one value.** TLC expands `\A self \in S : WF_v(p(self))` into one formula per
element of S, each in a context binding `self` to it (`Liveness.java:336-366`: `tool.contexts`
enumerates S, then `astToLive(tool, body, con1)`), and `LNAction.eval` evaluates the subscript and
then the body in that context (`LNAction.java:66-85`). The front end keeps the context as the
atom's scope, a chain of `ScopeBinding::Value`s below the model's (`get_bound_values`). So each atom
is `p(self)` under one value v of `self`, which no `\E` of Next pairs with: PlusCal writes
`Next == (\E self \in S : p(self)) \/ ...`, StarkMutex `\E self \in 1..N : i(self)` with
`i(self) == in1(self) \/ ...` and fairness over each `in1(self)`. Matching adds:
- an `\E` of Next whose bound names the action doesn't pair: each name is *pinned* once the action
  reads, where Next reads it, a name its scope binds to a value v that is an integer, string or
  model value, and the `\E`'s set is one the matcher reads without evaluating anything and that
  holds v: a declared constant, an interval of numbers and constants, an enumeration of those, a
  union of these, or a definition of one without effects (`holds_scalar`). The piece is (n, ρ)
  with ρ(name) = v: the choice of v from S is in C(n, ρ), and the walk makes it, since S is the
  same value at every state and holds v. A name pinned twice must be read as the same value; a
  pinned name the piece's atom never reads matches nothing, since the piece would hold under every
  value of it.
- on Next's side alone, an application of a global operator that isn't recursive: the walk goes
  into its body with each parameter bound to its argument, so a parameter whose argument is a
  pinned name stands for the same value. A parameter whose argument is anything else, a paired
  name included, matches nothing: from another call site it may stand for a value outside the
  paired set, where a pinned name's value is checked as the walk takes it (below).
- a disjunction of Next, into one disjunct (the choice is in C(n, ρ)); an action that is a
  disjunction takes each of its disjuncts from pieces of its own.

The claim's induction carries over with the pinned names fixed: the context between Next's root
and n is made of disjuncts chosen, one-item conjunctions, operator bodies, and values chosen, none
of which is a guard. (⇐) A path through n with each pinned name equal to its value has
C(n, ρ) ∧ n[ρ] true of (s, t(π)), and A is n[ρ] up to its names. (⇒) Where A(s, t) is TRUE, the walk
from s takes the value v of S, as it takes every value, reaches n under ρ and, by the induction,
generates t.

So the bit must be set exactly where the walk is under ρ. The walker keeps the `\E`s whose bodies
it compiles (`Compiler::binders`: the node, the bound's position, the slot its name takes), and a
continuation compiled inside the body is compiled with them popped, since it continues the walk
after the `\E` (`walk_exists`); a fresh walk, as ENABLED compiles, starts with none. A piece with
pins wraps the walk of n in a test that each pinned slot holds its value (`Id` equality, which for
these values is TLC's `equals`), and sets the bit only then. A walk through n elsewhere, or under
another value, sets no bit, which it needs not: the path under ρ generates every t A holds of.

The atom is evaluated where the action never reads a pinned name, where the `\E`'s set is one the
matcher can't read (`\E self \in {p \in S : pc[p] # "Done"}`) or doesn't hold v, where v isn't a
scalar, where an argument isn't a pinned name, and where the compiled walk never went through a
piece inside its `\E`s. Under a CONSTRAINT, where the steps aren't labelled, StarkMutex's 45 atoms
answer from 6 bytes of bits a step.

*Tests against TLC at d8fb231* (`prove-it-cli/tests/processes`, each as it stands, where the labels
answer, and under `CONSTRAINT Always`, where the bits do, at one and four workers): PlusCal's
`fair process` over an interval, two process sets with WF on both, `fair+` (SF), a process waiting
on a guard, model values, a constant set under a definition of it, WF on some processes and on an
action that is no process's, and a Next whose `\E` is over a set of the state. They fail where
the pinned test is dropped (the bit set under any value), where the bits or the labels' answers
are inverted, and where an atom answers from any label. The grid `prove-it-cli/tests/process-grid`
has 216 specs: fairness over a process `P(self) == a(self) \/ b(self)`, under WF and SF, over `a`,
and over `a` and `b` StarkMutex's way; Next's `\E` over P, over the disjunction written out, and
twice; its set an interval, an enumeration, a constant, a definition, a union and a set of the
state; and the fairness over the same set, a subset, and a superset with a value no `\E` takes.
Weak is fair over the pieces and AliasWeak over copies `P(self) /\ TRUE` that are none, plain and
under a CONSTRAINT: each run prints TLC's output beside it, at 1 and 4 workers.

**Fallbacks** (evaluate as today). Fall back where:
- the atom's action does not map exactly onto the split;
- it prints, draws, sets or reads registers, or reads TLCGet;
- it contains ENABLED, `\cdot`, or `[B]_w` inside;
- a step from the state took the shortcut past a walk (`is_enabled_exact` false);
- A is under another context than Next's instance (INSTANCE substitutions, a property in another
  module), unless the split matches exactly;
- the guard's shape is unsafe;
- the search stopped early or declined.

CONSTRAINT and ACTION_CONSTRAINT are fine for action atoms: TLC checks only in-model steps, and
those are the steps recorded. They are not fine for ENABLED from steps.

**Constraints from the lead** (`answer_atoms` owner):
- the table must be identical on the helper path (`on_helpers`/`Run::action`) and on the one-thread
  `Evaluator`, UNKNOWN included;
- an atom whose evaluation can fail still comes out UNKNOWN, then `atom_failure`, then the
  interpreter's report;
- labels decide only A's truth; the subscript test stays as it is on both paths.

**Constraints from the liveness climber** (branch `live-shared-levels`): threads record edges and
the merge resolves them, so labels must be appended wherever edges are and merged in the same
order. Agree the layout before building. One label (or one bit per atom) per edge costs about
90 MB on cf1s's 22.4M steps. Record it only when an atom uses it, and measure the non-liveness path.

**Tests, against TLC itself and not only the interpreter:**
- WF and SF over Next, over a sub-disjunction, and over a non-subset (falls back);
- a type-mixed spec on which predicate evaluation must raise, and one on which it must not;
- a successor generated first by a piece outside A and then by one inside A;
- a successor already seen from another parent;
- at 1 and 4 threads.

**TLC for those tests.** The Maven build of tlaplus needs the Toolbox target platform, so build the
jar from d8fb231 with `javac` instead:

```sh
cd tlaplus/tlatools/org.lamport.tlatools
find src -name '*.java' > sources.txt
javac -nowarn -encoding UTF-8 -proc:none -cp "$(find lib -name '*.jar' | tr '\n' :)" -d classes @sources.txt
(cd src && find . -type f ! -name '*.java' -exec cp --parents {} ../classes \;)
(cd classes && for jar in ../lib/*.jar ../lib/*/*.jar; do unzip -qo "$jar" -x 'META-INF/*'; done)
printf 'Main-Class: tlc2.TLC\n' > manifest.txt && jar cfm tla2tools.jar manifest.txt -C classes .
```

Leave the test libraries (junit, easymock, hamcrest, jacoco, javacc, cglib, objenesis, jgit) out of
the unzip.
