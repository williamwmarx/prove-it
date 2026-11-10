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

TLC's own times on this machine, on one worker and on every core, are in the section below once
measured.

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

### Not on the list

- A JIT or native code: the backend is shelved (native-backend.md), and the workspace stays std
  only.
- Hashing ids with a cheaper hash in the state table: it is already a multiply-shift.

## Results

Each change, measured with the suite against the build before it: median wall seconds of 5
interleaved runs on the 4-core cloud container, with the min–max range. Models not listed moved
within their range.

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
