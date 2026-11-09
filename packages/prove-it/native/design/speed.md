# Speed: as built

Notes on the native engine's speed work, kept out of DESIGN.md so they don't conflict with other
workstreams. The guard and memo work through #75 is in DESIGN.md's "M7 as built (guards)". The
native backend is shelved; [native-backend.md](native-backend.md) records why.

## Against TLC at 1, 4 and 16 threads

On `depot-ubuntu-24.04-16` (AMD EPYC 9R45, 16 cores), `main` at 148cdae. TLC was built from the
benchmark's pinned commit and run with `-workers 1`, `4` and `16`. Prove It's binary was run with
`PROVE_IT_ENGINE_BACKEND=rust` and `PROVE_IT_WORKERS` 1, 4 and 16. Times are median wall seconds of
3 interleaved runs, start-up included. Every run agreed with TLC's counts.

| Model | 1 thread (TLC / Rust) | 4 threads | 16 threads |
|---|---|---|---|
| Commit | 4.05 / 0.28 = 14.5× | 1.89 / 0.18 = 10.5× | 1.48 / 0.15 = 9.9× |
| Philosophers | 1.27 / 0.12 = 10.6× | 0.87 / 0.10 = 8.7× | 0.88 / 0.10 = 8.8× |
| Queue | 0.45 / 0.04 = 11.2× | 0.47 / 0.04 = 11.7× | 0.53 / 0.04 = 13.2× |
| MCbtree | 21.57 / 0.71 = 30.4× | 6.90 / 0.33 = 20.9× | 3.72 / 0.26 = 14.3× |
| SimpleRegular | 3.00 / 0.54 = 5.6× | 1.66 / 0.32 = 5.2× | 1.54 / 0.25 = 6.2× |
| SyncCons | 0.46 / 0.05 = 9.2× | 0.76 / 0.05 = 15.2× | 0.71 / 0.05 = 14.2× |
| 2PCwithBTM | 0.38 / 0.05 = 7.6× | 0.37 / 0.05 = 7.4× | 0.42 / 0.04 = 10.5× |
| VoucherRedeem | 0.53 / 0.05 = 10.6× | 0.45 / 0.05 = 9.0× | 0.50 / 0.06 = 8.3× |
| test19 | 0.69 / 0.09 = 7.7× | 0.81 / 0.07 = 11.6× | 0.79 / 0.07 = 11.3× |
| MCBakery | 6.20 / 0.79 = 7.8× | 4.56 / 0.47 = 9.7× | 4.43 / 0.43 = 10.3× |
| MCLamportMutex | 9.10 / 2.09 = 4.4× | 3.95 / 1.01 = 3.9× | 3.27 / 0.63 = 5.2× |
| MCSingleNode | 3.48 / 0.45 = 7.7× | 1.40 / 0.32 = 4.4× | 1.27 / 0.29 = 4.4× |
| MCDisruptor_MPMC | 2.40 / 0.20 = 12.0× | 1.13 / 0.19 = 5.9× | 0.91 / 0.19 = 4.8× |
| Paxos_MC | 5.63 / 0.78 = 7.2× | 2.06 / 0.80 = 2.6× | 1.49 / 0.79 = 1.9× |
| ReadersWriters | 1.46 / 0.11 = 13.3× | 1.05 / 0.11 = 9.5× | 1.08 / 0.11 = 9.8× |
| TokenRing | 1.17 / 0.19 = 6.2× | 0.89 / 0.18 = 4.9× | 0.93 / 0.18 = 5.2× |
| ACP_SB_TLC | 0.86 / 0.10 = 8.6× | 0.82 / 0.09 = 9.1× | 0.85 / 0.08 = 10.6× |
| Chameneos | 0.72 / 0.07 = 10.3× | 0.88 / 0.07 = 12.6× | 0.92 / 0.07 = 13.1× |

Geomean: 9.3× at 1 thread, 8.0× at 4 and 8.1× at 16. Rust is faster than TLC on every model at
every thread count. The five slowest relative to TLC at 16 threads, and why:

1. **Paxos_MC** never shared a level: about 690 states per level, under the 2,048 a level needs
   to be shared, though each state costs about 100 µs. Fixed by sharing on predicted work (below).
2. **MCSingleNode**: about 230 of its 765 ms is the TypeScript front end, which runs on one
   thread. The Rust lowering (F8) removes it.
3. **MCDisruptor_MPMC**: levels of about 1,400 cheap states, so sharing doesn't pay, plus the same
   front-end start-up. Also for F8.
4. **TokenRing** (and **ReadersWriters**): short runs, about 1 s, mostly start-up, which threads
   don't help. The whole check, temporal properties included, runs natively; F8 shortens the
   start-up.
5. **MCLamportMutex** scales 3.3× on 16 threads, but its CPU time grows from 2.1 to 4.8 s, so
   each state costs more on many threads. Not yet profiled.

## Sharing a level by its predicted work

A level is shared between threads when it has at least 2,048 states (`PROVE_IT_SHARED_LEVEL`).
It is also shared when the previous level's time per state predicts at least 8 ms of work on one
thread. Each thread takes at least half of 2,048 states, or at least 2 ms of the predicted work,
whichever gives more threads.

The time per state is the previous level's wall time, times the threads it ran on, divided by its
states, so it estimates one thread's cost. Which levels are shared changes nothing the search
finds: #70's shared expansion gives the same states, counts and logs as one thread.

Engine time on the 4-core cloud machine, `PROVE_IT_WORKERS` 1 then 4, after the change:
- Paxos_MC: 946 → 478 ms. Before, it stayed at 789 ms on 4 threads, as its levels from 7 to 23
  states now go to 4 threads, where only the three of 2,048 states or more went to 2.
- MCDisruptor_MPMC: 193 → 196 ms, against 220 → 204 before. Its levels stay under 8 ms.
- Commit: 382 → 250 ms, against 398 → 262 before.
- MCbtree: 791 → 349 ms.
- MCLamportMutex: 2,553 → 1,367 ms.

## Closure-level gains after the native backend

The native backend's experiment (native-backend.md, section 9) pointed back at the closures. What
came of it:

- **Applying a run of integers in place (#133).** `Store::apply` answers a tuple, or a function over a run of integers, at an integer in its domain, with a subtraction and a load, inline. Philosophers' search went from 1,518M to 1,401M instructions.
- **A PlusCal `pc` switch (#137).** A disjunction each of whose walks starts with `f[k] = c` of the same variable and bound name reads `f[k]` once, and enters only the walks whose constant matches.
  - It fires on 54 of the 772 passing corpus models, mostly PlusCal translations.
  - MCBakery went from 10.44B to 9.04B instructions.
- **Tuples of different lengths told apart in place (#141).** MCLamportMutex went from 16.77B to 16.30B instructions.

Tried and dropped:
- **Not memoizing trivial arithmetic.** Arithmetic is never marked costly, so it was never memoized. Philosophers' memo tables hold set and function constructions at about 99% hits.
- **Extending the switch to `f[i][j]` and `#`.** It fires on MCLamportMutex's three receive actions, which lead with `network[q][p] # << >>`. But the search went only from 16.77B to 16.75B instructions. The channels are usually non-empty, so all three actions still run.
- **Shifting fingerprints by a carry-less multiply.** Shifting by L zero bytes is multiplying by x^(8L) mod the polynomial. With PCLMULQDQ or PMULL, that is three carry-less multiplies and a Barrett reduction, with 8 bytes per length instead of a 16 KB table.
  - It is bit for bit the same as the tables, but slower in wall time: MCbtree went from 0.68 to 0.81 s, and MCBakery from 0.65 to 0.70 s.
  - The suite's models meet few lengths, so their tables stay in cache. Eight independent loads from L1 beat a chain of three dependent multiplies behind a call that can't be inlined, since the multiply needs its own target feature.
  - It could only win where the tables miss the cache. The branch is `fingerprint-multiply`.

## Where the suite's instructions go

Callgrind on the 18 suite models after #137, every model native. Each figure is a function's self cost as a share of its model's search, averaged over the models:

| Group | Mean share | Largest |
| --- | ---: | --- |
| Walker dispatch | ~30% | `segment` 11.6%, `build_equal` guards 7.5%, memo lookups 5.2%, `exists_step` 3.4% |
| Fingerprints | ~16% | `get_child` 6.8%, `shift_by_table` 5.0%, `set_parent` 1.9% |
| Store | ~8% | `find_in_block` 2.6%, `apply_other` 1.6%, `apply_field` 1.5% |
| Search | ~7% | `visit_successor` 3.3%, `search` 2.7%, `States::find` 1.1% |
| Allocation and copies | ~3.5% | `memcpy`, `malloc`, `free` |

In `segment` the cost is spread across closure entry and exit, the match on each op, and the bookkeeping and undo of assignments. No line stands out.
