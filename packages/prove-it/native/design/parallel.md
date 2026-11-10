# The parallel search, as built

The level-synchronous search that DESIGN.md section 4 plans, from the branches `store-overlay` (#59)
and `parallel-rust-search`. Where the code differs from the plan, the code wins, and this records
how.

- **No shared store, an overlay per thread.** 4.3's sharded, locked store would have put a lock
  or an atomic on every intern of the one-thread search. Instead the store stays a plain `&mut`
  store, and for a shared level it moves behind an `Arc`, unchanged while the threads run. Each
  thread interns in an **overlay** of its own (`Store::overlay`, `attach`):
  - The overlay keeps a copy of the store's values, blocks and texts. When it is laid on again it
    copies only what the store added since, because a store only adds values until it is reset.
  - It numbers its own values after that copy, so ids, offsets and text indexes are plain indexes
    in every store, as before.
  - It looks up a value in the store's intern table and string maps first, then in its own. A
    value the store holds therefore has the store's id in every overlay, and equal values still
    have equal ids.
  - Reading the store's values through a branch instead of a copy cost the one-thread search 10%
    more instructions on SimpleRegular; with the copy it costs 0.4%. What the copy costs is memory:
    one copy of the store's arrays per thread.
  - No `unsafe`, no locks; the crate's one `unsafe` block is still M7's prefetch.
- **Candidates per thread, merged in key order.** A thread claims runs of the level with an atomic
  cursor (up to 32 states, fewer when the level is short, so that every thread gets several) and
  expands each state with the one-thread code: `Search` is generic over where it finds and adds
  states (`Reached`).
  - A state found before the level is a duplicate.
  - Otherwise the thread keeps the first occurrence it reaches itself, with the concrete state, its
    key and its fingerprint. Under a VIEW or symmetry each occurrence carries its own state, so a
    winning key never takes another occurrence's state (4.1's case that breaks a key-only update).
  - At the barrier the coordinator walks the claimed runs in order, and within each run its
    thread's candidates in the order found. That is (parent, step) order without a sort.
  - It adds each candidate whose fingerprint isn't in the set yet, importing its values from the
    thread's overlay into the store (`Store::import`, parts first). That gives the numbering,
    parents, out-degrees and depth of TLC's one worker.
  - Where the search records a graph for liveness, each thread records its states' steps too,
    each to a state by the index `Candidates::index` gives it: a state found before the level by
    its own, and one the thread found by the index it would have if the thread's states all
    joined the store (the slots of those `Candidates::find` returns are marked `SEEN`). The merge
    resolves each of a parent's candidates to the index it takes, its own or that of the state
    with its key found first, and then appends the parent's steps in the order generated,
    duplicates included, with their labels and, under a VIEW or symmetry, the states they reached,
    imported. Its successor and new-state counts, its edge offset and the depth so far, TLC's
    diameter, follow: the graph of TLC's one worker. The bounds the one-thread search checks
    before it expands a state of a graph (`MAXIMUM_GRAPH_STATES`, 32-bit indices) stop the merge
    at that state, which the one-thread path then expands and stops at.
  - A thread's caches forget only what they hold of its overlay's own values (`forget_from`), so
    memo tables, fingerprints and symmetry images stay warm from level to level.
- **Stops (4.2).** A thread that stops at state `p` lowers an atomic `stop` to `p` and quits. The
  others finish every state before `stop` and skip the rest.
  - The merge keeps the candidates and generated counts of the states before `stop`. The rest of
    the level then runs on one thread, from `p`: it expands `p` again and stops there as the
    one-thread search does, with the violation's trace and counts, or the error's place, that TLC
    reports. A thread keeps none of that, so a stop that ended the level at once left the native
    binary nothing to print, and the TypeScript CLI an interpreter to hand over to. A state earlier
    in the level that would stop it stops it first.
  - `PROVE_IT_STOP_AT` inside a shared level is a stop at that state.
  - Where the key is the state, an invariant that fails of a successor a thread takes for new
    stops it at once: if another thread found that state first, its parent is earlier and stops
    the search first. Under a VIEW or symmetry the state another thread found first can be another
    state with the same key, whose invariant TLC checks instead, so the thread only records the
    failure, an invariant false or one that fails to evaluate, and the merge stops there only if
    that successor's key is still new when its parent's turn comes.
- **How many threads.** In the binding, `PROVE_IT_WORKERS`. In the native binary, TLC's
  `-workers` (`auto` is every core), which `PROVE_IT_WORKERS` overrides, so Parity can run on four
  threads under the `-workers 1` its recordings were made with. Either way at most
  `available_parallelism`, since more threads than the machine runs at once only take turns. The
  coordinator waits on the threads it spawned, and no thread spins.
- **The first level** is the initial states, and is shared like any other.
- **Where it runs on one thread.** A level runs on one thread when:
  - it has fewer than `PROVE_IT_SHARED_LEVEL` states (default 2,048, `MINIMUM_SHARED_LEVEL` as
    in `search.ts`), or too few for two threads of half that each;
  - the search records a graph for liveness and `PROVE_IT_TEST_LIVE_CHECK_AT` asks for a check
    of it at a state, which could be inside a level;
  - something prints or reads `TLCGet("distinct")`;
  - ToString makes strings, which it ranks as it evaluates them;
  - `PROVE_IT_LIVE_CHECK` is on.

  Each level then still runs on the fast one-thread path. VIEW, symmetry, constraints and
  `PROVE_IT_FP_VERIFY` all share levels.
- **The liveness checker's atoms** are answered on helper threads, each on an overlay of the store
  (`on_helpers`), unless something prints, draws, reads or sets TLC's registers, ranks strings
  with ToString, caches with TLCCache or builds a function TLC keeps lazy: a helper has none of
  the search machine's registers, generator, cache or functions. A helper starts with the search
  machine's values of the definitions TLC computed once at startup, so it never computes one again:
  SpanTreeRandom's `Edges`, drawn with RandomElement, gave each helper a graph of its own.
- **Contention.** Two things threads wrote to that they all read made two threads each run at half
  speed on Commit: the record-field position hint, now written only when it changes, and a
  thread's registers next to another's, now on cache lines of their own.
- **Not done.** Threads are spawned for each shared level; keeping them alive between levels would
  save the spawn, unmeasured. The merge is the serial part: 10–25% of a level's time on Commit at
  four threads on the 4-core cloud machine. A collision that only
  `PROVE_IT_FP_VERIFY` would count can be counted differently on more than one thread, since a
  thread compares a duplicate with its own first occurrence.

## Acceptance, as run

- **State logs: met.** `tla-engine/tests/search.rs` compares the outcome, counts, checkpoint and
  state log with `PROVE_IT_FP_VERIFY` at 1, 2, 4 and 16 threads (as many as the machine runs),
  sharing every level, on:
  - 2PCwithBTM, VoucherRedeem, SyncCons and MCEcho;
  - TLCGetLevel (deadlock) and test216;
  - view_symmetry (VIEW and SYMMETRY);
  - ReadersWriters (liveness: the graph, its labels and its stops at PROVE_IT_STOP_AT);
  - and 2PCwithBTM stopped by `PROVE_IT_STOP_AT` at eight states, inside levels and at their ends.

  Commit's state logs at 1, 2 and 4 threads are byte-identical (282,251 states).
- **Unit tests: met.** With `auto` taking the Rust search on more than one thread, `bun test
  tests/unit` passes 3,109 tests with the addon, and with four threads and every level shared
  (`PROVE_IT_WORKERS=4 PROVE_IT_SHARED_LEVEL=1`), 0 fail; 3,007 pass without the addon.
- **Parity with threads: met.** Parity on Depot with `PROVE_IT_WORKERS=4`, `PROVE_IT_SHARED_LEVEL=64`
  and `auto` taking the Rust search:
  - conformance 770 match;
  - differential tlc/ts 1,460 same + 6 known, ts/interpreter 1,466, ts/stopped 982, ts/rust
    1,466/1,466, rust/stopped 984/984;
  - engine coverage: the same outcome on and off on every model.
- **Speed: one thread unchanged.** Compare on `depot-ubuntu-24.04-4`, 9 interleaved runs, against
  `main`: the suite's geomean is 0.997×, every model within 3%.
- **Speed: many threads.** On `depot-ubuntu-24.04-16`, medians of 5, wall ms, Rust on one thread on
  `main`, then the TypeScript parallel search and Rust at 4 and at 16 threads:

  | Model | Rust, 1 | TS, 4 | Rust, 4 | TS, 16 | Rust, 16 |
  |---|---|---|---|---|---|
  | Commit | 286 | 379 | 184 | 367 | 141 |
  | btree | 654 | 724 | 322 | 1,939 | 246 |
  | SimpleRegular | 501 | 666 | 340 | 794 | 259 |
  | MCLamportMutex | 1,803 | 1,489 | 1,081 | 3,206 | 666 |
  | MCSingleNode | 431 | 904 | 320 | 1,166 | 290 |
  | Philosophers | 124 | 141 | 100 | 143 | 89 |
  | MCBakery | 723 | 929 | 737 | 954 | 732 |
  | Paxos_MC | 780 | 1,101 | 760 | 1,079 | 748 |

  Rust at 16 threads is 2.0× one thread on Commit, 2.7× on btree and MCLamportMutex, and 1.9× on
  SimpleRegular. It is within noise of one thread on the models whose levels are short or whose
  states are all initial (MCBakery, test19, TokenRing). It is faster than the TypeScript parallel
  search on every one of the 18 models, at 4 and at 16 threads. Every verdict agrees with TLC.

## Handoff: retiring the TypeScript engine's parallel search

Since #85 (0.2.3), `auto` sends every search the Rust engine accepts to Rust at any thread count.
The TypeScript engine's own threads now run only when `PROVE_IT_WORKERS>1` and Rust does not take
the search:

- `PROVE_IT_ENGINE_BACKEND=ts`;
- no addon for the platform, or an ABI mismatch;
- `getEngineIneligibility` in `src/check.ts`, a bailout, or a hand-over from the native engine.

In each of these cases, the TypeScript engine then runs on one thread. That is correct and only
slower, which is what replaces the TypeScript engine's threads.

### Code to remove

- `src/engine/parallel.ts`: the shared state table, `runLevel` and `serveLevels`.
- `src/engine-worker.ts`: the worker thread.
- `src/engine/workers.ts`: `spawnEngineWorkers`.
- In `src/engine/search.ts`, the `parallel` record, `searchInParallel`, `canShare`,
  `WORKER_SPAWN_MS`, `MINIMUM_SHARED_LEVEL`, `seeded`, `tlc.isShared`, and the
  `parallel.workers?.terminate()` call. `threads` in the result becomes 1, so check whether
  `EngineResult.threads` is still needed.
- In `src/engine/store.ts`, shared mode, which is everything below `// --- shared mode ---`:
  - `SharedStore`, `shareStore`, `attachViews`, `internShared`;
  - every `if (shared)` branch, `freezeTexts`, and the `isTextFrozen` bail.
  - The Rust overlay does not depend on any of it. Keep `transfer.ts`: the native IR and the state
    log use it.
- In `src/engine/context.ts` and `src/engine/settings.ts`, whatever only the workers used. Check
  each export with a grep once the files above are gone.
- In `scripts/build.ts`, `scripts/build-binary.ts` and `scripts/run.ts`, the
  `"src/engine-worker.ts"` entry.
- In `src/check.ts`:
  - `workers: getEngineThreads()` in the `runEngine` call;
  - the `MissingBuildFileError` rethrow in the catch at the end of the engine's run. Keep it if the
    interpreter's workers (below) still raise it through this path.

### Keep, out of scope

These are the interpreter's parallel search, not the engine's:

- `src/parallel.ts` (`check` and `checkParsed`, public through `index.ts` and `cli/tlc.ts`);
- `src/parallel-worker.ts`;
- the shared fingerprints in `src/fingerprints.ts`;
- `src/worker.ts`, which the prover's workers also use.

The interpreter's parallel search runs only with `PROVE_IT_ENGINE=0`. Retiring it would change
the public `check` and is a separate decision for the owner.

### Tests

| Test | After retiring |
| --- | --- |
| `tests/unit/state-log.test.ts`, "writes the same states with 1 and 4 threads when the workers take levels" (pins `ts`) | Delete it. The Rust state-log determinism at 1/2/4/16 in `tla-engine/tests/search.rs` and `native-search.test.ts` replaces it. Keep the one-thread `ts` runs. |
| `tests/unit/parallel.test.ts`, "the shared state table" | Delete it: it tests `engine/parallel.ts` directly. |
| `tests/unit/parallel.test.ts`, "check with workers matches TLC" | Keep it: it tests `check` with workers. With the addon, it now runs the Rust search. Check that every case still passes without the addon (one TypeScript thread) and with `PROVE_IT_ENGINE=0` (the interpreter's workers). The workers case for "grows the fingerprint table that workers share" is the interpreter's; leave it. |
| `tests/unit/state-graph.test.ts`, "writes the graph of a single TLC worker when several are asked for" (`workers: 2`) | Keep it: `-dump` is ineligible for the engine and goes to the interpreter on one worker. |
| `tests/unit/store-trace.test.ts`, `engine.test.ts`, `native-runs.ts` | Grep for `PROVE_IT_WORKERS`, `shareStore` and `isShared`. Drop the `ts`-backend multi-thread cases. Keep the Rust ones. |

Check-ins: the macOS Rosetta step runs `native.test.ts` and `native-search.test.ts`. The exit-255
crash came from the TypeScript workers under Rosetta, so watch whether it stops after this change.
The speed session owns the overlay's cross-level caching in `tla-values/src/store.rs`, `memo.rs`,
`Worker::attach` and `forget_from`. None of this change touches them.
