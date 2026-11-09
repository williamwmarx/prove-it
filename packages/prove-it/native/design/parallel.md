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
  - A thread's caches forget only what they hold of its overlay's own values (`forget_from`), so
    memo tables, fingerprints and symmetry images stay warm from level to level.
- **Stops (4.2).** A thread that stops at state `p` lowers an atomic `stop` to `p` and quits. The
  others finish every state before `stop` and skip the rest.
  - The merge keeps the candidates and generated counts of the states before `stop`, so the
    checkpoint is the one-thread search's, with the reason the one-thread search gives for `p`. A
    state earlier in the level that would stop it stops it first.
  - `PROVE_IT_STOP_AT` inside a shared level is a stop at that state.
  - Where the key is the state, an invariant that fails of a successor a thread takes for new
    stops it at once: if another thread found that state first, its parent is earlier and stops
    the search first. Under a VIEW or symmetry the state another thread found first can be another
    state with the same key, whose invariant TLC checks instead, so the thread only records the
    failure, an invariant false or one that fails to evaluate, with its reason, and the merge stops
    there only if that successor's key is still new when its parent's turn comes.
- **How many threads.** `PROVE_IT_WORKERS`, at most `available_parallelism`, since more threads
  than the machine runs at once only take turns. The coordinator waits on the threads it spawned,
  and no thread spins.
- **The first level** is the initial states, and is shared like any other.
- **Where it runs on one thread.** A level runs on one thread when:
  - it has fewer than `PROVE_IT_SHARED_LEVEL` states (default 2,048, `MINIMUM_SHARED_LEVEL` as
    in `search.ts`), or too few for two threads of half that each;
  - the search records a graph for liveness;
  - something prints or reads `TLCGet("distinct")`;
  - ToString makes strings, which it ranks as it evaluates them;
  - `PROVE_IT_LIVE_CHECK` is on.

  Each level then still runs on the fast one-thread path. VIEW, symmetry, constraints and
  `PROVE_IT_FP_VERIFY` all share levels.
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
  - ReadersWriters (liveness, one thread by design);
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
