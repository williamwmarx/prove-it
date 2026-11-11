# Porting the prover to Rust

The plan for moving Prove It's proof checker, the obligation generator and its four back ends,
from TypeScript to Rust. It covers what there is, how "the Rust prover is right" is measured,
where the code goes, the stages, and what speed to expect. It follows DESIGN.md's method: each stage
lands behind a differential with the TypeScript path still the default, the default flips only
once the Rust path matches everywhere, and then the TypeScript is deleted.

Status: phase 1 (this document). No port code yet. Numbers marked *measured* come from the
4-core cloud container (Node 22.23.4, Bun 1.4.4) on `main` at de3a9f8.

---

## 1. Inventory

### 1.1 The parts

`src/prover` holds 77,047 lines, `src/obligations` 8,873. With them, 85,920 lines of TypeScript,
about 9.5 times the TypeScript engine the model checker replaced.

| Part | Lines | Files | What it is |
|---|---|---|---|
| `obligations/` | 8,873 | 21 | tlapm's front half: the TS AST to tlapm's parse trees (`source.ts`), anonymization to de Bruijn indices (`anonymize.ts`, `normalize.ts`), module flattening and instances (`module.ts`), proof simplification (`simplify.ts`), obligation generation (`generate.ts`), levels, temporal norms, subexpression references, `ENABLED`/`\cdot` lambdification (`action.ts`), method pragmas, and tlapm's obligation printer with a port of OCaml's `Format` (`printer.ts`, `format.ts`). Output: `PrintedObligation`s, each a `Sequent` of tlapm's E_t plus the text tlapm prints. |
| `prover/prep/` | 2,202 | 7 | tlapm's Prep: methods and their time limits (`methods.ts`), `normalize_expand`, `flatten`, triviality, the action frontend (`action.ts`), the ENABLED axioms and LevelComparison frontends, and the obligation fingerprint (`fingerprint.ts`, `md5.ts`). |
| `prover/smt/` (encoder) | 2,676 | 10 | tlapm's SMT encoding: TLA+ to SMT-LIB over one sort `Idv` (`encode.ts`, `rewrite.ts`, `axioms.ts`, `data.ts`, `flatten.ts`, `extensionality.ts`, `instances.ts`, `table.ts`, `format.ts`, `context.ts`). |
| `prover/smt/solver/` (core) | 23,254 | 69 | A port of Z3 4.x as `z3 -smt2 AUTO_CONFIG=false smt.MBQI=true` runs tlapm's UFNIA problems: hash-consed AST and Z3's own hashes and hash tables, the SMT-LIB parser, the rewriters (`rewriter-tpl`, `arith-rewriter`, `poly-rewriter`, `nnf`, `der`, `qe-lite*`, `pull-quant`, `propagate-values`, `maximize-ac-sharing`), the tactic pipeline, the CDCL kernel with E-graph, relevancy and dynamic Ackermann (`context.ts`, `internalizer.ts`, `conflict-resolution.ts`), E-matching with the MAM (`mam-*`, `e-matching.ts`), MBQI with the model finder and checker (`model-*`, `proto-model.ts`, `auf-solver.ts`), and the LRA theory glue (`theory-lra-*`). |
| `prover/smt/solver/lp/` | 14,502 | 46 | Z3's `math/lp`: the LAR solver, simplex core, bound propagation, integer solver with cuts and the Diophantine equations solver, and the NLA solver (`nla-*`: monomial bounds, tangent lemmas, Gröbner bases over PDDs, interval arithmetic via cross-nested forms). |
| `prover/smt/solver/nlsat/` | 7,875 | 12 | Z3's nlsat: polynomials, univariate factorisation, real algebraic numbers, interval sets, the explain module and levelwise projection. |
| `prover/zenon/` | 11,594 | 38 | A port of Zenon as tlapm ships it, with its TLA+ extension (`tla/`): the `.znn` reader, the tableau search, the low-level proof translation (`mltoll.ts`), the Isar printer (`isar*.ts`), and an independent proof checker (`check/`) that every proof must pass before it counts. |
| `prover/isabelle/` | 11,713 | 50 | A port of the parts of Isabelle2025 TLAPS uses: the Pure kernel (`pure/`: terms, types, `thm`, unification, higher-order patterns, the rewriter and simplifier, nets), classical reasoning, hypsubst and blast (`provers/`), Isar's outer and inner syntax, type inference and methods (`isar/`), and the Isabelle/TLA+ object logic decoded from a generated 509 KB JSON (`tla/logic-data.ts`, made by `scripts/isabelle-logic.ts` from tlapm's heap). The encoder (`encode.ts`) writes the theory tlapm writes. |
| `prover/ptl/` | 739 | 4 | tlapm's PTL path: the encoder to LS4's syntax and a decider (a tableau over a CDCL SAT solver) standing in for LS4. |
| `prover/tlapm/` | 502 | 3 | tlapm's fingerprints file (`.tlacache`) in OCaml's Marshal format (`ocaml-marshal.ts`, `cache.ts`), and the `tlapm` back end that runs a real tlapm (`tlapm.ts`). |
| `prover/*.ts` | 1,362 | 8 | `prove.ts` (the driver: methods in turn, fingerprint reuse, ordering, CASE-error numbering, reports), `decide-pool.ts` and `prove-worker.ts` (worker threads), `deciders.ts`, `verdict.ts`, `first-order.ts`, `ocaml.ts`, and `tlaps-module.ts` (TLAPS.tla verbatim). |

### 1.2 The pipeline and its seams

```
 source text ──► src/lexer + src/parser (mode "tlapm") ──► TS AST
                  │
 obligations/ ────┘ source ─► normalize/anonymize ─► simplify ─► generate ─► PrintedObligation[]
                                                                            (Sequent, text, kind)
 prover/prove.ts, per obligation, in tlapm's order:
   findMethods ─► fingerprint ─► reuse? ─► normalizeExpand ─► isTrivial?
   for each method:  ENCODER[prover](sequent) ──► text ──► DECIDER[prover](text) ──► verdict
                     smt:      action ─► flatten ─► smt/encode       ─► smt/solver   (Z3 port)
                     zenon:    action ─► flatten ─► zenon/encode     ─► zenon        (Zenon port + checker)
                     isabelle: action ─► flatten ─► isabelle/encode  ─► isabelle     (Isabelle port)
                     ls4:      ptl/encode                            ─► ptl          (LS4 stand-in)
```

The decisive fact for the plan: **every back end takes text and returns a verdict.** `DECIDERS` in
`deciders.ts` mapped a prover name to `(text, {timeLimitMs, signal}) => Verdict`, and the worker
pool already ships only `{prover, text, timeLimitMs}` across a thread boundary. Each decider is a
port of a separate program whose input is the file tlapm writes (`.smt`, `.znn`, `.thy`, LS4's
input), so each can be ported, tested and switched on alone, exactly at that seam.

### 1.3 The dependency graph

Group-level imports, computed from the sources (`errors` omitted, which everything uses):

```
obligations          -> ast, lexer, parser            (the TS front end)
prover/prep          -> obligations
prover/ptl           -> obligations, prep, verdict
prover/first-order   -> obligations
prover/smt (encoder) -> obligations, ocaml
prover/smt/solver    -> verdict, lp, nlsat
  lp                 -> solver/{array, hashtable, lbool, random-gen, rational, rlimit}, nlsat
  nlsat              -> solver/{lbool, random-gen, rational, rlimit}, lp
  core               -> lp (theory-lra-* only), nlsat/algebraic (one import)
prover/zenon         -> obligations (encode.ts only), first-order, verdict, zenon/check, zenon/tla
  zenon/check        -> zenon (its expressions only; shares no logic with the search)
prover/isabelle      -> obligations (encode.ts only), first-order, verdict, isar, pure, tla
  pure               -> (nothing)
  provers            -> pure
  isar, tla, tools   -> pure, provers, each other
prover/prove         -> everything above, worker
prover/tlapm         -> prove, ../ (the library, to run real tlapm)
```

What this gives:

- **The deciders depend on no obligation code.** `smt/solver`, `zenon` (all but `encode.ts`),
  `isabelle` (all but `encode.ts`) and `ptl/{sat,tableau,decide}` only read text. They can be ported
  and tested on their own, in parallel, and none needs the front end.
- **Inside the SMT solver**, six small utility files (`array`, `hashtable`, `hash`, `lbool`,
  `random-gen`, `rational`, `rlimit`; about 900 lines) are the whole interface `lp` and `nlsat` need
  from the core. So after a shared foundation, the arithmetic (`lp` + `nlsat`, 22,377 lines) and the
  core (23,254) are independent ports that meet only in `theory-lra-*` (2,141 lines of glue).
- **Inside Isabelle**, `pure` depends on nothing, `provers` only on `pure`; `isar` and `tla` come
  last.
- **The encoders and Prep need obligations**, and obligations needs a TLA+ parser in tlapm's mode.
  That is the one part with a front-end dependency.

### 1.4 What the prover needs from outside

| Need | Today | In Rust |
|---|---|---|
| Lexer and parser, tlapm's mode | `src/lexer.ts`, `src/parser.ts` `parseTlapmModule` (24 branches on `isTlapm`: keywords, `@`, LAMBDA, incomplete-expression errors, operator grouping), and its tokens | `tla-front`'s lexer and parser, which already have proofs in the AST (`ast.rs`: `Proof`, `ProofStep`, `Theorem`), gain a tlapm mode (section 3.5); `obligations/regroup.ts` (tlapm's `Pco.resolve`) moves with the obligations. |
| SANY levels | not used: obligations has its own `levels.ts` (tlapm's `Expr.Levels`) | ported with obligations, not taken from `tla-front`'s `levels.rs` (different rules). |
| The evaluator, values | not used | — |
| Rationals and big integers | JS `bigint` (17 files, all in `smt/`) | a std-only integer type (section 3.4). |
| Threads | `worker.ts` workers via `decide-pool.ts` | std threads (section 3.7). |
| Clock and cancellation | `Date.now()` deadlines, `AbortSignal` | `std::time::Instant` natively; a host clock import in WebAssembly; an atomic cancel flag (section 3.6). |
| MD5 | `prep/md5.ts` (60 lines) | ported. |
| OCaml stdlib behaviours | `ocaml.ts`, `zenon/ocaml.ts` (`Hashtbl.hash`, `List.sort`), `obligations/format.ts` (`Format`), `tlapm/ocaml-marshal.ts` | ported bit-exactly, each with its licence (section 3.8). |

### 1.5 How it is called today

- **Library:** `prove(options)` is the only export (`src/index.ts`), with the types `ProveOptions`,
  `ProveResult`, `ProofObligation` and its three variants. `ProveOptions` has `source`,
  `loadModule`, `backend` (`"tla-ts"` default, or `"tlapm"` to run a real tlapm in Node or Bun),
  `signal`, `onObligation` and `workers`.
- **CLI:** `prove-it tlapm …` (`src/cli/tlapm.ts`) reproduces tlapm's command line and its toolbox
  protocol on stderr: `-N`, `--summary`, `--strict`, `--toolbox`, `--line`, `--printallobs`,
  `--threads` (default `availableParallelism()`), `-I`, `--noproving`, `--nofp`, `--nofpl`,
  `--safefp`, `--cleanfp`, `--usefp`, `--cache-dir` (or `TLAPM_CACHE_DIR`). It calls
  `getObligations`, `proveObligations`, `formatNormalized`, `encodeProofTheory` and the
  fingerprint cache directly. The native binary declines it: `prove-it-cli/src/check.rs` prints
  `not native yet: tlapm`.
- **Workers:** with `workers > 1` and workers supported, `proveObligations` starts a decide pool:
  each worker runs `decide(prover, text, timeLimitMs)`; the pool dispatches the earliest obligation
  first, and up to four obligations per worker are in flight. Abort terminates the workers.
  Without workers every decision runs on the calling thread.
- **Settings:** no `PROVE_IT_*` variable reaches the prover today. `PROVE_IT_WORKERS` is the
  model checker's. `TLAPM_CACHE_DIR` is tlapm's.
- **Scripts:** `bench:prove` (`prove-benchmark.ts`), and the conformance scripts against tlapm's
  recorded results: `conformance:prove` (statuses per obligation against `proofs.json`),
  `conformance:smt`, `:zenon`, `:isabelle`, `:ptl` (each decider against the input tlapm sent and
  the verdict its back end gave), `conformance:smt-encode`, `:isabelle-encode` (encodings against
  tlapm's), `conformance:tlapm` (CLI output against `tlapm.json`), `conformance:sany`
  (`proof-conformance.ts`). The decider and encoder conformance scripts need `.proofs/`, the inputs
  `conformance:record-proofs` captures from a real tlapm; no CI job runs any of them, and this
  container has no tlapm.
- **Tests:** `tests/unit/{prove,prove-workers,obligations,obligation-isabelle,obligation-zenon,ptl,
  smt,smt-clause-store,smt-intervals,smt-nlsat,smt-pdd,zenon,isabelle,tlapm-cache}.test.ts`: about
  140 tests, 3,060 lines. The `smt-intervals`, `smt-nlsat` and `smt-pdd` tests drive `lp/` and
  `nlsat/` classes directly.

---

## 2. The oracle

"The Rust prover is right" means: **on every obligation of every corpus, it reaches the verdict
the TypeScript prover reaches, for the same reason, with the same text.** TypeScript is the oracle
until the flip, as the TS engine was for the model checker; tlapm's recorded results stay the
external reference both are measured against.

### 2.1 What must be identical, and what may differ

Identical, compared byte for byte:

- every `PrintedObligation`'s `text`, `location`, `kind` and id, and everything `prove-it tlapm`
  prints (stdout, the toolbox messages on stderr, the exit code);
- every encoder's output: the SMT-LIB, `.znn`, theory and LS4 text for every method of every
  obligation, and the fingerprint;
- every decider's verdict on every input, **under a deterministic budget** (2.3);
- each back end's deterministic statistics, which show it ran the *same search*, not just reached
  the same answer: for SMT, Z3's `rlimit` count at the end and the number of quantifier instances
  (`checkSmt` already returns both); for Zenon, the `-stats` numbers `runZenon` returns (nodes
  searched, maximal branch, proof nodes, formulas created) and the Isar proof text; for Isabelle
  and PTL, step counters this plan adds to the TypeScript first (stage P0);
- each `ProofObligation`'s `status`, `prover` and `reason` text, and the theory
  `encodeProofTheory` writes;
- error texts: every `TlaProofError`, `TlaProverError` and `TlaUnsupportedError` message.

May differ:

- timing: `timeUsedMs`, and so which obligations reach a wall-clock limit;
- an obligation the TypeScript gives up on for a reason that is a property of JavaScript, not of
  the algorithm: a stack overflow (`isStackOverflow` → `unknown` in `smt/solver/solver.ts` and
  `isabelle/decide.ts`) or V8's heap filling (`rlimit.ts` `isHeapNearlyFull`). These already
  differ between Node and Bun. The differential lists them; the Rust answer must equal the
  TypeScript answer on a larger stack/heap (run once with `node --stack-size` raised), or be
  `unknown`.

Never allowed: a verdict that contradicts the TypeScript or tlapm (`unsat` where they say `sat`,
or the reverse), a proof of what tlapm's back end refuted, or a crash where TypeScript returns an
answer.

### 2.2 The layers

1. **The unit tests**, unchanged, run against the Rust path once it is the default: the about 140
   tests above through `prove`, `decideSmt`, `decideZenon`, `decideIsabelle`, `decidePtl` and
   `getObligations`. Tests that drive TypeScript internals (`smt-intervals`, `smt-nlsat`,
   `smt-pdd`, `smt-clause-store`, `zenon`'s checker tests) are ported to Rust unit tests in the
   crate that ports the code, case by case, and deleted from TypeScript only with the code they
   test.
2. **The decider corpus** (`scripts/prover-inputs.ts`, P0): every text `prove` sends a backend on
   the corpus modules of `proofs.json`, which methods it tries following what the earlier ones
   answered, written once to `.prover-inputs/<prover>/<digest>.<ext>`, with the TypeScript
   decider's verdict, statistics and step limit (2.3) in `tests/conformance/prover-inputs.json`.
   Replaying the record writes the same inputs on any machine in minutes. This is the per-back-end
   test set and needs no tlapm. Its size is in 2.4.
3. **The decider differential** (`scripts/prover-differential.ts`, P0): decides every input of
   the decider corpus with its step limit, by the Rust port through the addon (until every
   TypeScript decider was deleted, `--side ts` decided by the TypeScript), and compares verdict
   and statistics with the record;
   `--prover smt|z3|zenon|isabelle|ls4`, `--jobs`, `--filter`, as the other conformance scripts. It
   reports `same`, `differs` (verdict or statistics), `unstable` (a runtime limit, 2.3),
   `declined` and `crash`. The gate is zero `differs`, `declined` and `crash`.
4. **The encoder differential** (with stage P5): the Rust obligation pipeline writes, for every
   corpus obligation, the printed obligation, the fingerprint and every encoder's text; they must
   equal the TypeScript ones byte for byte. Together with layer 3 this covers `prove` end to end,
   because a verdict is a function of the text.
5. **The end-to-end differential** (with stage P6): `prove` and `prove-it tlapm` (JS and native
   binary) on every corpus module, TypeScript against Rust: identical `ProofObligation`s (less
   timing) and identical CLI output, with the reuse paths (`.tlacache`, `--nofp`, `--nofpl`) on
   the tlapm corpus.
6. **tlapm's records**, as today: `conformance:prove` must not regress on either path (same
   counts of matches, deviations, misses), and the encoder conformance scripts keep comparing with
   tlapm wherever `.proofs/` exists. A Depot job that installs tlapm and records `.proofs/` once
   would make layers 2–3 checkable against tlapm's own back ends too (Z3, Zenon, Isabelle, LS4);
   that is the coordinator's call, since it is paid CI.
7. **Self-checks:** Zenon's independent checker stays mandatory in Rust. Every Rust `unsat` from
   the SMT port on the decider corpus is cross-checked against the TypeScript verdict (layer 3),
   and `sat` answers against tlapm's records where present.

### 2.3 Deterministic budgets

Every decider stops at a wall-clock deadline (`Date.now()` in `rlimit.ts`, `zenon/limits.ts`,
`isabelle/pure/interrupt.ts`, `ptl/decide.ts`), which is part of tlapm's semantics and stays. A
verdict near the deadline therefore depends on the machine, and a Rust port that is faster will
prove more. That is allowed in production but makes a poor oracle. So the differential runs both
sides **without a deadline and with a step limit**, as built in P0:

- **Steps.** Every check of a decider's limits is a step (`Steps` and `isStepLimitReached` in
  `verdict.ts`): each `inc` of Z3's resource limit, whose count was already Z3's `m_count` and
  seeds MBQI; each `getLimitFailure` of Zenon's search, checker and printer; each
  `checkInterrupt` of Isabelle; each `isExpired` of the PTL decider. Past the step limit a decider
  gives up exactly as at its deadline. Without a limit nothing changes (the unit tests and the
  re-recording of 2.4 show it).
- **A step limit per input.** Steps per second differ about sixfold between inputs of one
  backend, so no single limit stands for tlapm's time limit. `prover-inputs.ts --record` decides
  each input twice: first with tlapm's time limit, which gives the steps the backend takes within
  it on the recording machine, then with those steps as the step limit and no deadline. The
  second answer, its statistics and the step limit are recorded in
  `tests/conformance/prover-inputs.json`. From then on the record is a fact about the input, not
  the machine: any port, on any machine, at any load, must give the same answer and statistics
  from the same step limit.
- **Unstable answers.** A full heap (V8's, in `rlimit.ts`) or stack ends a decision for a reason
  of the runtime, not the search. The record keeps the reason as the statistic `stop`, and the
  differential reports such inputs as `unstable` instead of comparing them.

### 2.4 The baseline

The corpora (`bun scripts/fetch-corpora.ts`, `tests/conformance/corpora.json`), as tlapm recorded
them in `proofs.json`:

| Corpus | Modules | Obligations |
|---|---|---|
| tlapm (`library`, `test`, `examples`) | 205 | 9,256 |
| examples (tlaplus/Examples) | 74 | 17,831 |
| tlc (TLC's test models) | 18 | 3,161 |
| community (CommunityModules) | 6 | 2,889 |
| spectacle | 1 | 0 |
| **total** | **304** | **33,137** |

tlapm's results on them: 20,502 trivial, 12,523 proved, 112 failed. Proved by back end: SMT
10,934 (plus 64 by the `z3` method), Zenon 793, Isabelle 476, LS4 359, others (`fail`, `cvc4`,
`cooper`, `expandenabled`, `expandcdot`) 8. Back-end runs recorded: SMT 11,164 (10,891 unsat, 259
unknown, 14 sat), Zenon 921 (792 unsat), Isabelle 477 (389 unsat). tlapm's provers report 1,124 s
in total.

The TypeScript prover on the same modules (*measured*, Node 22, `proveObligations` on one thread
per module, three modules at once, 4.5 GB heap; 34 min wall, 6,793 s CPU in all):

| Status | tlapm | TypeScript |
|---|---|---|
| trivial | 20,502 | 20,502 |
| proved | 12,523 | 12,490 (SMT 10,862, Zenon 820, Isabelle 392, LS4 358, `z3` 58) |
| failed | 112 | 143 |
| unsupported | — | 2 |
| modules that fail before any obligation (`TlaProofError`) | 9 | 9 |

Decisions the TypeScript made, by back end (attempts, not obligations; reuse not counted):

| Back end | Decisions | unsat | unknown | sat | Time | Mean |
|---|---|---|---|---|---|---|
| SMT (`smt`) | 10,599 | 10,269 | 316 | 14 | 2,201 s | 0.21 s |
| SMT (`z3` method) | 61 | 55 | 5 | 1 | 202 s | 3.3 s |
| Zenon | 960 | 803 | 157 | — | 1,387 s | 1.4 s |
| Isabelle | 482 | 372 | 110 | — | 1,763 s | 3.7 s |
| LS4 (PTL) | 346 | 345 | — | 1 | 3 s | 0.01 s |

Where the 6,102 s of per-module wall time went: deciding 5,555 s (91%), Prep and encoding 520 s
(8.5%; `tcp_proof` alone 140 s, the two `BPConProof`s 67 s each), generating obligations 27 s
(0.5%). The slowest modules are dominated by Isabelle and Zenon: `LamportMutex_proofs` 1,270 s
(Isabelle 543 s, Zenon 391 s, SMT 326 s), `Boulanger` 653 s, `tcp_proof` 406 s, `Bakery` 303 s.

With Node's default heap (about 2 GB per worker), `bench:prove` with `--jobs 4` lost two
modules to "JavaScript heap out of memory": `rlimit.ts`'s heap check stops Z3 work, but the
heap filled elsewhere (in `EWD998PCal_proof` and one of the next three largest), which kills the
whole process. The run above raised the heap to avoid that. This is a TypeScript defect the Rust
port removes; it is noted here so that P0's comparison runs use the same raised heap.

Under Bun (*measured*, the same three modules of 5.1 run as one process each, three at once,
against the Node run above):

| Module | Node | Bun | Ratio | Bun's results |
|---|---|---|---|---|
| `EWD998PCal_proof` | 18.0 s | 45.6 s | 2.5× | the same |
| `FiniteSetTheorems_proofs` | 19.3 s | 36.8 s | 1.9× | one Zenon proof fewer: it reached the 10 s limit |
| `AtomicBakeryWithoutSMT` | 33.1 s | 46.7 s | 1.4× | the same |

The whole corpus was not run under Bun: at these ratios it takes one to two hours on this
machine, and the three modules show what matters, that the runtime already changes verdicts at
the limits.

Time by verdict, from a second run of the same corpus with each decision's time kept
(*measured*; 5,649 s of per-module wall time in all):

| Back end | unsat: count, time, mean | unknown: count, time, mean |
|---|---|---|
| SMT (`smt`) | 10,282, 498 s, 0.05 s | 303, 1,622 s, 5.35 s (limit 5 s) |
| SMT (`z3` method) | 55, 61 s, 1.1 s | 5, 140 s, 28 s |
| Zenon | 803, 301 s, 0.37 s | 143, 957 s, 6.7 s (limit 10 s) |
| Isabelle | 370, 152 s, 0.41 s | 98, 1,352 s, 13.8 s (limit 30 s) |
| LS4 | 345, 3 s, 0.01 s | — |

So successful decisions take about 1,015 s and decisions that end `unknown` about 4,071 s: 80% of
the deciding is spent on obligations that are not proved, most of it waiting for a limit. (SMT's
mean `unknown` exceeds its 5 s limit because the clock is read every 256th step.)

**The runs disagree.** The second run proved 10,875 obligations with SMT and failed 132; the
first proved 10,862 and failed 143. About a dozen obligations sit near a limit and fall either way
with the machine's load. That is the case for 2.3's step budgets: the oracle must not be a
wall-clock run.

---

## 3. Architecture

### 3.1 Crates

All in the existing workspace under `native/crates/prover/<name>`, std only, `license` per crate
where it ports non-MIT code (3.8). P0 made each one; the backends' crates decline every input until
their port lands. `crates/prover/clippy.toml` applies to all of them and refuses iterating a std
hash map or set and unstable sorts (3.6).

| Crate | Ports | Depends on | Lines (TS) |
|---|---|---|---|
| `prove-decide` (`decide/`) | `verdict.ts`: `Verdict`, `Decision` with its statistics, `DecideError` (`Prover` for malformed input, `Declined`), and `Limits` (deadline, step limit, cancel cell, and the host's clock in WebAssembly) | — | ≈100 new |
| `prove-num` | `smt/solver/rational.ts`'s integers and rationals, as a std-only big integer (3.4) | — | ≈600 new |
| `prove-smt` | `smt/solver/` with `lp/` and `nlsat/`, as modules `util`, `lp`, `nlsat`, `core` | `prove-num` | 45,631 |
| `prove-zenon` | `zenon/` but `encode.ts`, with `check/` as its own module that shares nothing with the search | — | ≈11,300 |
| `prove-isabelle` | `isabelle/` but `encode.ts`; `logic-data` embedded with `include_bytes!` in a compact binary form generated by `scripts/isabelle-logic.ts` | — | ≈11,250 + data |
| `prove-ptl` | `ptl/sat.ts`, `tableau.ts`, `decide.ts` | — | ≈500 |
| `prove-obligations` | `obligations/`, `prep/`, every encoder (`smt/*.ts`, `zenon/encode.ts`, `isabelle/encode.ts`, `ptl/encode.ts`, `first-order.ts`), `ocaml.ts`, `tlaps-module.ts`, the `.tlacache` format | `tla-front` (parser only) | ≈16,700 |
| `prove-it-prover` | `prove.ts`, `deciders.ts`, the decide pool as threads: the driver and the one entry point the bindings and the CLI call | all of the above | ≈700 |

The deciders depend on nothing of each other, so they compile and test in parallel and a session
can own one crate. `prove-it-host` gains a `decide` and a `prove` operation, `prove-it-napi` and
`prove-it-wasm` expose them, and `prove-it-cli` gains `tlapm` at the end (P6).

Nothing here touches `tla-engine`, `tla-values`, `tla-live` or `tla-ir`. `tla-front` gains a tlapm
parse mode (3.5), announced to the coordinator before it starts.

### 3.2 The boundary during the migration

Like the engine, the Rust prover arrives through the addon and the WebAssembly module, and
TypeScript keeps the orchestration until P6:

```
 prove.ts (TS)            decide(prover, text, limits) ──► native decide  (addon / wasm)
```

- One binding call, as built in P0 (`prove-it-host/src/prover.rs`, ABI 12): `decide(prover,
  text, timeLimitMs, stepLimit | undefined, cancel | undefined)` returns `{kind: "decided",
  verdict, statistics}`, `{kind: "error", message}` (thrown as a `TlaProverError`) or `{kind:
  "declined", reason}`. It runs on a thread with a 256 MB stack. Strings cross once per decision; a
  decision takes milliseconds to seconds, so the 15–160 ns crossing (DESIGN 10.1) is noise.
  WebAssembly exports it as `prove_it_decide` through the `call()` ABI and reads the clock from the
  `prove_it_now` import the engine already uses.
- `src/prover/deciders.ts` chose per prover while TypeScript deciders remained:
  `PROVE_IT_PROVER=ts|rust` forced all, and `PROVE_IT_PROVER_<NAME>=ts|rust` one back end, the
  default flipping to `rust` in the PR that made its differential clean (`RUST_BACKENDS`). With
  every TypeScript decider deleted, that choice is gone: `decide` calls the native engine, a port
  that declines its input is a `TlaProverError`, and where no engine loads `prove` follows
  `check`'s rule (fallback.md): the WebAssembly module, or `EngineUnavailableError`.
- The worker pool keeps working: each worker calls the addon synchronously. Cancellation cannot
  reach a thread inside a native call by `worker.terminate()`, so the pool hands each worker a
  cell of a `SharedArrayBuffer` (`DecideOptions.cancel`) and sets it when it stops; the N-API
  binding reads the cell in place, and `Limits::is_canceled` is where a Rust backend checks it, as
  the TypeScript checks `signal.aborted`. A WebAssembly decision runs on the thread that would set
  the cell, so it has none.
- `decide` needs no files: its input is the text. Where Rust reads modules (P5 and P6, for
  `loadModule`, `-I` and tlapm's library), it uses the host's request-and-retry convention from
  the SANY retirement's stage (a) (`prove_it_host::sources::Sources`): the export takes the
  `known` pairs, returns `{kind: "needed", keys}` for what it lacked, and JavaScript answers and
  calls again; no callback into JavaScript. The keys are its `module:<name>`, plus any new kind
  tlapm's lookup needs, added to the list in `sources.rs`. Both exports go through the wasm
  `call()` buffer ABI and bump `ABI_VERSION` as it requires.
- At P5 the boundary moves up: `getObligations` and the encoders run in Rust, behind
  `prove_obligations(source, modules) → obligations + texts`, and `prove.ts` only decides. At P6
  the whole of `prove` and `prove-it tlapm` run in Rust; the TS `prove` becomes a thin call, as
  `check` is.

### 3.3 Terms

Each back end already has its own term representation, chosen by the program it ports; the Rust
port keeps each one's semantics, including where sharing is observable:

- **SMT:** Z3's `ast_manager`: a hash-consed DAG with ids in creation order, hashed with Z3's
  Jenkins hash (`hash.ts`), stored in Z3's open-addressing tables (`hashtable.ts`), whose slot
  order the model finder iterates. In Rust: one arena per check (`Vec<Node>`, `u32` ids), the same
  hash on `u32` with wrapping arithmetic, the same table with the same probe and growth. Reference
  counting (`ref-vector.ts`, `expr-ref.ts`) and id recycling are ported literally, `inc_ref`,
  `dec_ref` and temporaries included, not dropped: recycled ids order Z3's sorts and the matcher
  hashes small ids, so they steer the search (`native/design/smt-core.md` §2).
- **Zenon:** hash-consed expressions whose equality is alpha-equivalence and whose hash ignores
  bound names, one store per run so that fresh names restart. In Rust: an arena per run with the
  same hash (`zenon/ocaml.ts`'s `Hashtbl.hash` port).
- **Isabelle:** de Bruijn lambda terms whose rebuilders return the same object when nothing
  changes, with cached `maxidx`, loose-bound and flag summaries. In Rust: `Rc<Term>` with
  `Rc::ptr_eq` as the fast path, the summaries in the node. Terms are immutable and never shared
  across threads, so `Rc`, not `Arc`. Blast's prototerms keep their mutable variables as shared
  cells (`Rc<RefCell<Option<BlastTerm>>>`, compared by pointer), with the undo trail as now: an
  arena would put a variable table into the signature of every term function, so the files
  would no longer port literally, and it would only grow over a search, while the cells are freed
  as JavaScript frees them. Unification checks occurrence before every assignment, so no cell
  can reach itself and nothing leaks.
- **Obligations:** tlapm's E_t with de Bruijn indices and the `Sequent`/`Hyp` context. In Rust:
  `Rc`-shared trees like `tla-front`'s AST, which already uses `Rc` for definitions and theorems.
  Several `WeakMap` caches keyed by object identity (`prove.ts` `incompleteCaseHyps`, five in
  `obligations/`, four in `isabelle/`) become caches keyed by `Rc` pointer or by an id stored in
  the node.

### 3.4 Integers and rationals with std only

JS `bigint` appears only in the SMT solver (17 files; `rational.ts`, `lp/`, `nlsat/`, the numeral
parser). `prove-num` provides `Int`: an `i64` inline with a `Vec<u32>` magnitude when it
overflows, with exactly JS `bigint`'s semantics: `/` truncates toward zero, `%` takes the
dividend's sign, `>>` floors, and decimal printing and parsing. `Rational` is `rational.ts` on top
(normalised, positive denominator), with Z3's `div`/`mod` as `rational.ts` defines them. Division
is Knuth's algorithm D; multiplication schoolbook (operands in tlapm's problems are a few limbs).
It is tested against JS `bigint` by a generated table of operations (random operands of 1–8 limbs
and the edge cases), checked in, and fuzzed in `native/fuzz`. Nothing else in the workspace has a
big integer yet; `tla-values` is free to use this one later.

### 3.5 What the front end must add

`obligations/index.ts` uses `src/lexer.ts` and `parseTlapmModule`, and `source.ts` converts the TS
AST. It uses nothing else of the TS front end: no resolution, no SANY levels (tlapm's levels are
its own, in `obligations/levels.ts`). Both TS parsers are on their way out, so the Rust
obligations read `tla-front`'s AST (`ast.rs`, which mirrors `src/ast.ts`). What they need from
`tla-front`, behind a `ParseMode::Tlapm` flag and without changing SANY's mode:

- the parse in tlapm's mode: the 24 places `parser.ts` branches on `isTlapm`: keywords and
  `TRUE`/`FALSE`/`BOOLEAN`/`STRING` read only as keywords, `@` kept as a token, string columns,
  tlapm's "incomplete expression" and "Unexpected keyword" errors, LAMBDA, `\B`/`\O`/`\H`
  prefixes, RECURSIVE inside LET, the separated definables, and no SANY operator-grouping fix-up;
- the token stream, which `index.ts` uses to place tlapm's TAB error after the last token before
  the first tab and to find the module's end;
- a syntax failure in the shape tlapm prints, `{reason, line, column, isEnd}` (today
  `TlaSyntaxError.failure`).

`regroup.ts` (tlapm's `Pco.resolve`, 99 lines: `SUBSET S \ T` is `SUBSET (S \ T)` to tlapm) is
not part of the parse: `source.ts` applies it while converting. It moves with the obligations
(P5b), so `tla-front`'s AST stays a faithful parse in both modes. Pragmas `(*{ … }*)` are comments
to the lexer and `obligations/pragma.ts` reads them from the source text, so they need nothing.

The gate (agreed with `tla-front`'s owner): a `tlapm-ast` mode of `scripts/front-differential.ts`
comparing the TS parser's tlapm-mode AST, tokens and syntax failures with `tla-front`'s, over the
corpora including the 304 modules of `proofs.json` and the modules they load, and the error
corpus of `tests/conformance/tlapm.json`. P5b's byte-identical obligation texts check it end to
end. This is P5a; it is the only work in a crate another session owns, so it is announced to the
coordinator first, done by or with that crate's owner, and kept to that flag.

### 3.6 Limits, interruption, determinism

- **Limits** stay what they are: a wall-clock deadline per decision from the method's time limit
  (tlapm's semantics), checked where the TypeScript checks it (every 256th Z3 step, every Zenon
  step, each Isabelle interrupt point, each PTL iteration), plus the cancel flag. In WebAssembly,
  `Instant` is not available on `wasm32-unknown-unknown`, so the module imports a `now()` from the
  host, as it imports `prove_it_report` today. The step budget of 2.3 is a second, optional
  limit. No new timeouts.
- **Memory:** where V8's heap would fill, the TS SMT solver answers `unknown`. Rust has no such
  ceiling in-process; it counts the AST manager's nodes and stops at a fixed cap, as Z3's
  `max_memory` does, so an obligation cannot take the process down.
- **Stack:** recursion that overflows in JS answers `unknown`. Rust cannot catch an overflow, so
  each decision runs on a thread with a large stack (256 MB, like the engine's search thread), and
  the deep recursions the TS relies on catching (the rewriters, Isabelle's unifier and simplifier)
  carry a depth counter that ends the decision with `unknown` before the stack does.
- **Determinism.** The TypeScript prover is deterministic given its inputs and a step budget,
  because JS `Map` and `Set` iterate in insertion order, `Array.prototype.sort` is stable, and
  every hash that orders anything is computed explicitly (Z3's, OCaml's). The port keeps that:
  - every `Map`/`Set` that is iterated (about 460 are created across the prover) becomes an
    insertion-ordered map (`tla-front`'s `ordered_map.rs`, or a `Vec` plus an index) or a `Vec`;
    `std::collections::HashMap` only for lookups never iterated, enforced by review and by a
    `clippy.toml` `disallowed-methods` on `HashMap::iter`/`keys`/`values` in the prover crates;
  - `sort` stays stable (`sort_by`, never `sort_unstable*`), with the comparators ported
    literally, including OCaml's `List.sort` (a merge sort whose ties differ from a stable sort's
    in places) where `zenon/ocaml.ts` ports it;
  - Z3's `random_gen`, seeded as it is from the `rlimit` count, Z3's hashes and OCaml's
    `Hashtbl.hash` are ported on `u32` with wrapping arithmetic (41 `Math.imul`/`>>> 0` sites);
  - floating point stays `f64` in the same operation order (Z3's activities and the LP settings),
    with no fused multiply-add; `Math.log`/`Math.log2`/`Math.ceil` appear twice (`pdd-solver.ts`,
    `tlapm/cache.ts`) on small integers, where `f64::ln` gives the same results (checked in the
    unit tests);
  - JS numbers used as integers beyond 2^31 (counters, ids) become `u64`/`usize`; those used as
    32-bit (`| 0`, `>>> 0`) become `i32`/`u32`.
- **Places the TypeScript could already depend on something unspecified**, to audit in P0 before
  the port relies on them: iteration over an object's keys (`Object.keys`, `for … in`) where keys
  look like integers, since JS orders those numerically, not by insertion; `Array.prototype.sort`
  without a comparator (string order); and `localeCompare`. Each one found is either documented
  as intended or fixed in TypeScript first, so that the oracle is itself well defined. A first
  pass found no `localeCompare` and no `for … in`; three `Object.entries`/`Object.values` over
  constant tables with non-numeric keys (`tlapm/cache.ts`, `smt/format.ts`, `obligations/
  module.ts`); and four comparator-less sorts, all of strings, which Rust reproduces as byte
  order on ASCII names: `zenon/isar.ts:1235` and `zenon/phrase.ts:19–20` (orders that reach the
  Isar text), and `lp/lar-solver.ts` `getTermKey` (only a canonical key, never iterated).

### 3.7 Threads instead of workers

Until P6, the existing pool. From P6, `prove-it-prover` runs the driver on the calling thread and
decisions on a pool of `--threads`/`workers` std threads, with the same order: the earliest
obligation first, at most four per thread in flight, an obligation waiting for the last earlier
one with its fingerprint, and the SMT encoder's CASE-error count taken from every earlier
obligation (`getSession`). That ordering decides what is reused and how CASE errors are numbered,
so it is ported exactly, and the end-to-end differential (2.2, layer 5) runs with 1 and 4 threads.
In WebAssembly, one thread.

### 3.8 Licences and notices

A port is a derived work, so each Rust file keeps the licence and the port header of the TS file
it ports, and each section of `THIRD_PARTY_NOTICES.md` names the Rust paths beside the TS ones
from the PR that ports them, and drops the TS paths in the PR that deletes them.

| Crate | Derived from | Licence | `THIRD_PARTY_NOTICES.md` once it is Rust |
|---|---|---|---|
| `prove-smt` | Z3 (`src/smt`, `src/ast`, `src/math/lp`, `src/nlsat`, `src/util`; `nlsat/` ports `src/nlsat` and `src/math/polynomial` of z3-5.3.3, limit checks included) | MIT | the Z3 section names `native/crates/prover/smt/`, which keeps `z3-license.txt` beside the code (the TypeScript solver, which kept it too, is deleted) |
| `prove-num` | Z3's `rational`/`mpz` semantics, written fresh on JS `bigint`'s rules | MIT (Z3's where it follows `rational.ts`) | under the Z3 section |
| `prove-zenon` | Zenon as tlapm ships it, with its TLA+ extension | BSD-3-Clause-style (INRIA) | the Zenon section names the crate; the crate keeps Zenon's `LICENSE` beside the code (the TypeScript Zenon, which kept it too, is deleted) |
| `prove-zenon` (`ocaml` module) | OCaml's `Hashtbl.hash` (`runtime/hash.c`), `List.sort`/`List.stable_sort` | LGPL-2.1-only with OCaml's linking exception | the OCaml section lists the Rust file |
| `prove-isabelle` | Isabelle2025's Pure, Isar, Provers (BSD-style, Cambridge/TUM), and Isabelle/TLA+'s theories and ML setup as tlapm ships them (BSD, tlapm's licence) | BSD-3-Clause-style | the Isabelle section names the crate, which keeps `LICENSE` and `LICENSE-tlapm` beside the code (the TypeScript Isabelle, which kept them too, is deleted) |
| `prove-ptl` | tlapm's PTL backend input; the decider is our own | MIT, tlapm's BSD for what `ptl/encode.ts` ports | tlapm section (no section named the TypeScript decider, which is deleted) |
| `prove-obligations` | tlapm (obligations, Prep, encoders, `.tlacache`, TLAPS.tla verbatim) | BSD-2-Clause-style (INRIA, Microsoft, Linux Foundation) | tlapm section |
| `prove-obligations` (`format`, `marshal`, the `getHash` of `action`) | OCaml's `Format` (`stdlib/format.ml`), Marshal (`runtime/intern.c`, `extern.c`), `runtime/hash.c` | LGPL-2.1-only with OCaml's linking exception | the OCaml section lists the Rust files |

The package's `"license": "MIT AND LGPL-2.1-only WITH OCaml-LGPL-linking-exception"` comes from
the OCaml ports alone (`tlapm/ocaml-marshal.ts`, `obligations/format.ts`, `action.ts`'s
`getHash`, and `zenon/ocaml.ts` until the TypeScript Zenon was deleted). Their Rust ports inherit it: they are translations of the same code. So
`prove-zenon` and `prove-obligations` declare `license = "MIT AND BSD-3-Clause AND
LGPL-2.1-only WITH OCaml-LGPL-linking-exception"` (the exact SPDX list fixed when the crate lands),
and the LGPL code stays in its own modules. The linking exception is what lets those modules be
linked statically into the addon, the WebAssembly module and the binary without the relinking
obligation of LGPL section 6; the condition left is to ship their source, which the repository and
the npm package do (the `.node`, `.wasm` and binary ship from this repository, and the crate
sources are public). The package's licence string does not change. The BSD-style licences require
the notices in binary distributions: the main package ships `THIRD_PARTY_NOTICES.md` (its
`files` and `prepack`), but the platform packages (`native/npm/<platform>`) and the release
archives of the binary do not yet; the first stage that links a ported back end into them adds it.

### 3.9 Size

Each stage reports what its crate adds to the three artefacts, measured from release builds on
the PR: `prove-it-engine.node` (linux-x64-gnu), `dist/prove-it-engine.wasm`, and the `prove-it`
binary, before and after, in bytes. The table lives in the Handoff section and grows by a row
per stage. Today, before any prover crate (*measured*, release builds on linux-x64-gnu at
b815883): `prove-it-engine.node` 2,224,024 bytes, the `prove-it` binary 5,678,520 bytes; the
WebAssembly module's size is taken in P0, where the `wasm32-unknown-unknown` target is installed.

The Isabelle/TLA+ logic (509 KB of JSON in `tla/logic-data.ts`, parsed once per process today)
is embedded in `prove-isabelle` with `include_bytes!` as a compact binary: `scripts/isabelle-
logic.ts` gains a second output, a string table plus the theorems as length-prefixed `u32`
records, written to `native/crates/prove-isabelle/data/logic.bin` and checked in beside a digest
the crate's test compares with the JSON, so the two cannot drift. Expected well under the JSON's
size (most of it is repeated names and JSON punctuation); it is decoded lazily once per process
into the term arena (`std::sync::OnceLock`). Decoding instead of `const` data keeps compile time
and the crate's source small. If the WebAssembly module's growth matters for browsers, the data
can also be fetched beside the module, as the module itself is; that is decided when P4b
measures it.

---

## 4. Stages

Every stage: the TypeScript stays the default until the stage's differential is clean on all
corpora; then a separate commit flips the default; the TypeScript it replaces is deleted only at
P7 (or earlier for a back end, once its Rust path has been the default through one release).
Sizes are TypeScript lines ported.

| Stage | Scope | Size | Tested against | Risk | Depends on |
|---|---|---|---|---|---|
| **P0** Harness | step counters and `stepLimit` in the TS deciders (2.3); the determinism audit of 3.6; `scripts/prover-inputs.ts` and `scripts/prover-differential.ts`; the `decide` binding in `prove-it-host`/`-napi`/`-wasm` with the cancel cell and the `now()` import; `PROVE_IT_PROVER*`; the `prove-*` crates as empty shells | ≈1,000 new | itself: TS vs TS through the binding must be `same` everywhere | low | — |
| **P1** PTL | `prove-ptl` | ≈500 | decider differential on the LS4 inputs; `ptl.test.ts`; `tests/conformance/ptl` | low | P0 |
| **P2** Zenon | `prove-zenon`: reader, search, LL proofs, Isar printer, the independent checker | ≈11,300 | decider differential on `.znn` inputs (verdict, stats, Isar text byte-identical); `zenon.test.ts` ported for the checker | medium: OCaml-specific orders (`Hashtbl`, `List.sort`) | P0 |
| **P3a** SMT foundation | `prove-num`; Z3's `hash`, `hashtable`, `lbool`, `random-gen`, `rlimit`, `array`, `dependency` | ≈1,500 | generated tables against JS `bigint`; hash and table iteration orders against TS | low | P0 |
| **P3b** SMT arithmetic | `lp/` and `nlsat/` | 22,377 | `smt-intervals`, `smt-nlsat`, `smt-pdd` ported to Rust; and a call trace: `PROVE_IT_LP_TRACE` records every `theory-lra-*` → `lar_solver`/`nla`/`nlsat` call and result on the SMT inputs, Rust replays it and must give the same results (DESIGN 6.6's store-op replay, for the LP) | high: the largest, numeric code | P3a |
| **P3c** SMT core | AST, parser, rewriters, tactics, CDCL kernel, E-matching, MBQI, `theory-lra-*` | 23,254 | decider differential on `.smt`/`.smt2` inputs (verdict, `rlimit` count, instances); `smt.test.ts`, `smt-clause-store.test.ts`. Until P3b lands, inputs without arithmetic theory atoms only, then all | high | P3a; all inputs need P3b |
| **P4a** Isabelle kernel | `pure/` | 6,628 | ported unit tests of the kernel; the decider differential on the theories whose tactics are only `pure` steps (few); mostly through P4b | medium | P0 |
| **P4b** Isabelle provers and Isar | `provers/`, `isar/`, `tla/`, `tools/`, the logic data | 5,124 + data | decider differential on theory inputs (verdict, step count); `isabelle.test.ts` | medium-high: Isabelle's search order (nets, simpsets) must be exact | P4a |
| **P5a** tlapm parse mode | `tla-front` `ParseMode::Tlapm`: the parse, the tokens, the syntax failure (3.5) | ≈400–600 in `tla-front` (its owner's inventory: `Mode::Tlapm` in `parser.rs`, `parse_tlapm_module`; the tokens and `SyntaxFailure` exist already) | `front-differential.ts tlapm-ast` against the TS parser on all corpus modules; tlapm's parse errors on `tlapm.json` | medium; touches a shared crate | announced; independent of P1–P4 |
| **P5b** Obligations | `obligations/` on `tla-front`'s AST, `regroup` included | 8,873 | encoder differential: every obligation's text, location, kind; `obligations.test.ts`; `conformance:tlapm`'s `-N`/`--summary` output | high: tlapm's printer and Format layout byte for byte | P5a |
| **P5c** Prep and encoders | `prep/`, the four encoders, `first-order`, fingerprints, MD5 | ≈5,800 | encoder differential: every back-end text and fingerprint byte-identical; `conformance:smt-encode`, `:isabelle-encode` | medium | P5b |
| **P6** Driver and CLI (4c) | `prove-it-prover` (`prove.ts`, ordering, reuse, CASE sessions, threads), `.tlacache` (OCaml Marshal), `prove-it tlapm` in the native binary, `prove` in the library through the binding | ≈2,000 | end-to-end differential (layer 5), with 1 and 4 threads, with and without `.tlacache`; `prove.test.ts`, `prove-workers.test.ts`, `tlapm-cache.test.ts`; `conformance:tlapm` | medium | P1–P5 |
| **P7** Delete | the TypeScript prover and obligations, `PROVE_IT_PROVER*`, the TS-only tests the Rust tests replaced; `THIRD_PARTY_NOTICES.md` | −86,000 | the whole gate, `conformance:prove` unchanged | low | P6 and every flip |

**P0 leaves the oracle as it is.** The step counters and `stepLimit` change TypeScript that is the
oracle, so P0 lands them inert: with no budget set, no counter is compared and no verdict can
change. P0's PR shows `prove` on all 304 corpus modules before and after, identical per
obligation (33,137 obligations; tlapm's counts are 20,502 trivial, 12,523 proved, 112 failed, and
the TypeScript's own counts are in 2.4), and the `rlimit` counts and Zenon statistics identical
on the decider corpus. The recorded TypeScript side of the decider corpus is produced under step
budgets, so it is reproducible: P0 records it twice and shows the two recordings identical (every
verdict and every statistic) before any Rust is compared against it. The two existing defects of
2.4, the verdicts that move near a wall-clock limit and the out-of-memory crash with Node's default
heap, are recorded there and not fixed in TypeScript beyond what the budgets need. The
per-obligation `setTimeout` yield of 5.1 is removed only if the whole corpus gives identical
results without it; otherwise it stays.

**P5a and the shared crates.** P5a is the only stage inside a crate another session owns. It is
announced to the coordinator before it starts. It builds on what the front session lands for
linking `tla-front` into the addon and WebAssembly (SANY's retirement, stage a), and the `decide`
binding of P0 follows the loader and ABI conventions the existing `check` and the coming
`check_sources` entry use (one call, encoded arguments, a result or a typed error), so the host has
one way to call Rust.

**What the interpreter's retirement means here.** The prover uses three helpers from
`src/worker.ts` (`spawnWorker`, `getParentPort`, `isWorkerSupported`) and nothing else of the
interpreter. Until P6 it keeps using them; at P6 the pool is std threads, and `prove` needs
nothing from `worker.ts`.

**Parallelism.** After P0, five tracks are independent and can go to separate sessions: PTL
(P1, then whoever finishes first), Zenon (P2), the SMT foundation then arithmetic (P3a → P3b), the
SMT core (P3c, after P3a's few days), Isabelle (P4a → P4b), and the front end and obligations
(P5a → P5b → P5c). P6 joins them. Each track owns its crate, so they do not conflict; the shared
files are `deciders.ts`, the binding and the docs, each touched in a few lines per stage.

**Flip order.** Each back end flips as soon as its differential is clean: PTL, Zenon, Isabelle and
SMT independently. Obligations and encoders flip together at P5c (the texts are identical by then,
so the deciders downstream see no change), and the driver at P6.

**First stage I take:** P0, then P1. P0 builds what every other track needs (the binding, the
differential, the deterministic budgets) and P1 proves it on the smallest back end; both are small
enough to land in one PR each. If the coordinator starts other sessions, they can begin on P2,
P3a and P4a against P0's `decide` interface as specified here before P0 merges, since the decider
crates are pure functions from text to verdict.

---

## 4a. How to port a back end

For the session that takes a track. Read this document, DESIGN.md §12 and AGENTS.md first.

**Naming and layout.** One crate per track, already made in P0 (`native/crates/prover/<name>`,
package `prove-<name>`), modules named after
the TS files in snake case (`lp/lar-solver.ts` → `lp/lar_solver.rs`), one Rust module per TS
file unless two are trivially small, so a reader can put the two side by side. Keep the port
header comment of each TS file (what it ports, from where, under which licence) and the
explanatory comments; keep TS names in snake case, so `getTermKey` is `get_term_key`. Errors
are `enum`s named after `src/errors.ts`'s classes (`SmtCanceledError` → `SmtError::Canceled`).
The entry point is the shell's `pub fn decide(text: &str, limits: &Limits) -> Result<Decision,
DecideError>` (`prove-decide`), which `prove-it-prover` calls by prover name: `Ok` with the
verdict and the statistics, `DecideError::Prover(message)` where the TypeScript throws a
`TlaProverError` (Z3's parse errors), and `DecideError::Declined(reason)` for input the port does
not cover yet, which TypeScript then decides. Declining is always allowed; a wrong answer never is.

**Porting literally.** The goal is the same search, step for step, not the same answer by
another route. So:
- a `Map` or `Set` that is ever iterated, spread, or turned into an array becomes an
  insertion-ordered map or a `Vec`, deletions included (JS keeps the order of the remaining
  entries; `Vec::remove`, not `swap_remove`); a `Map` used only with `get`/`has`/`set` may be a
  `HashMap`. The crate's `clippy.toml` disallows iterating `std` hash maps; an exception needs an
  `#[expect(clippy::disallowed_methods, reason = "…")]` that says why the order cannot matter;
- `array.sort(cmp)` is `slice.sort_by(cmp)` (stable, as JS), with the comparator ported
  literally, including a comparator that returns 0 for distinct items; `array.sort()` with no
  comparator compares the items' strings by UTF-16 code units, which is byte order only for
  ASCII, so port it as a sort of the strings and assert ASCII; an OCaml `List.sort` keeps its
  own merge;
- `| 0`, `>>> 0` and `Math.imul` are `i32`/`u32` wrapping operations; any other number used as
  an integer is `i64` or `usize`; a number used as a float stays `f64` in the same order of
  operations;
- `bigint` is `prove_num::Int`, whose `/`, `%` and `>>` follow JS;
- a JS exception used for control flow (`SmtCanceledError`, `TlaIsabelleError("Interrupt")`)
  becomes a `Result` propagated with `?`; never a panic;
- recursion that the TS relies on catching as a stack overflow gets a depth counter (3.6).

**Steps.** `Limits` is a cheap-clone handle with no lifetime (an `Rc`, steps in a `Cell`), so a
backend can keep clones in its closures and lazy sequences while a decision runs; every clone
counts the same steps, and none may outlive `decide`. A step is a check of the limits, and the
Rust port counts it at exactly the points the TypeScript does, with
`Limits::is_step_limit_reached` where the TypeScript calls `isStepLimitReached`, and
`is_step_limit_passed` where it compares without counting (Zenon's `getStopReason`): in `ResourceLimit.inc` for Z3, in `getLimitFailure` for Zenon (the search,
the checker and the Isar printer), in `checkInterrupt` for Isabelle, in `isExpired` for PTL. The
deadline and the cancel cell are checked where the TypeScript checks `Date.now()` and the signal.
The step count is the first statistic compared, and the cheapest witness of the same search.

**Statistics.** Each decider reports these, under the same names in both languages, in this
order; `prover-differential.ts` compares them field by field:
- SMT (`smt`, `z3`): `instances` (quantifier instances, absent when the search threw), `steps`
  (Z3's resource-limit count), and `stop` when it gave up early: `steps`, `time`, `signal`, `heap`,
  `stack` or `unsupported`;
- Zenon: `steps`, `nodesSearched`, `maxBranchFormulas`, `proofNodes`, `formulasCreated` (its
  `-stats`), `stop` (the search failure or the limit that stopped it), and `proof`, the length and
  FNV-1a hash of the Isar proof's UTF-16 code units (`getTextDigest`), when it found one;
- Isabelle: `stop` (the exception, such as `Interrupt`) when it gave up, and `steps`;
- PTL: `steps`. A
track that finds another cheap counter that pins the search (for example conflicts or decisions
in the SMT kernel) adds it to both sides in its own commit, inert in TS as P0's are.

**Running the oracle.** Once per machine, after `bun scripts/fetch-corpora.ts` and building the
addon (`bun scripts/platform-packages.ts build`):

```
NODE_OPTIONS=--max-old-space-size=4500 bun scripts/run.ts prover-inputs   # writes .prover-inputs/, minutes
bun scripts/run.ts prover-differential --prover zenon --jobs 4
```

The heap flag is needed: without it the solver's heap fills on two modules, their workers die,
and `prover-inputs` exits with an error, naming how many modules it lost.

`--update` writes the answers that differ into the record, `--filter` keeps the inputs
whose key, `prover/digest`, contains the text (`--filter /0` keeps about a sixteenth), and `.prover-differential.json` holds every result. Outcomes: `same`, `differs`,
`unstable` (2.3), `declined` (not covered by the port yet), `crash`. With
`PROVE_IT_ENGINE_WASM=dist/prove-it-engine.wasm` the decider is the WebAssembly module. A track
that changes a TypeScript decider (it should not need to) re-records with `prover-inputs --record`
in the same PR, under Node with `NODE_OPTIONS=--max-old-space-size=4500`.

**Tests.** Port the TS unit tests of the code you port to `#[test]`s in the crate, case for case,
with the same inputs and expected results; the TS tests stay until P7 deletes the TS code. Add a
test for every difference the differential found, with the smallest input that shows it.

**The gate before a flip commit.** On the whole decider corpus for the back end, under the
recorded step limits: zero `differs`, zero `declined` and zero `crash`, every `unstable` listed with
why; the
ported unit tests pass; the TS unit tests pass with `PROVE_IT_PROVER_<NAME>=rust`;
`conformance:prove` gives the same counts as on `main`; the wasm build passes the differential on
a sample (`--prover <name> --filter /0`); the size row is recorded (3.9); and the full local gate of
AGENTS.md passes. The flip itself is a separate commit that changes only the default, so it can
be reverted alone.

### 4b. The tracks

What each session starting a track needs, beyond 4a. Paths are under `packages/prove-it/src/prover`
unless they say otherwise; the crate is under `native/crates/prover/`. "First" lists the modules in
dependency order (computed from the imports), so each can be tested before the next. The first gate
is the TS unit tests named, ported to `#[test]`s; the corpus differential (4a) is the gate before
the flip. Every track must not touch:
- another track's crate;
- `tla-engine`, `tla-values`, `tla-live`, `tla-ir` or `tla-front`;
- the TypeScript prover, except to add a statistic to both sides (4a, with a re-recording in the
  same PR);
- `prove-decide`, the binding and `deciders.ts`, except through the lead (this document's owner).

**P2 Zenon** (`prove-zenon`, `zenon/`):
- In scope: `zenon/` (11,594 lines) but `encode.ts`, and `ocaml.ts`'s `Hashtbl.hash` and
  `List.sort`, which are LGPL (3.8).
- First: `limits.ts`, `ocaml.ts`, `expr.ts`, then `parse.ts`, `phrase.ts`, `proof.ts`. Then the
  search (`index-table`, `node`, `rules`, the rule files, `search.ts`), `mltoll`, `llproof`,
  `isar*`, and last `check/` (`terms` first). `check/` imports only `expr`, `parse`, `proof` and
  `limits`, so a second session could port it in parallel once those exist.
- First gate: `tests/unit/zenon.test.ts` (18 tests), whose inputs are under `tests/fixtures/zenon`.
- Statistics: 4a.

**P3a SMT foundation** (`prove-num` and the `util` module of `prove-smt`), taken first by the P3c
session:
- In scope: the JS-`bigint` integer of 3.4; `smt/solver/rational.ts`, `hash.ts`,
  `hashtable.ts`, `lbool.ts`, `random-gen.ts`, `rlimit.ts` (the step counting of 2.3, not V8's heap
  check), `array.ts`, and `lp/dependency.ts`, which `nlsat` uses.
- That is all `lp` and `nlsat` take from the core. Land it first so that P3b-lp and P3b-nlsat
  start from it.
- First gate: generated tables against JS `bigint` for `+ - * / % >> gcd` and printing, on
  operands of 1 to 8 limbs and the edge cases; Z3's hash of a few hundred keys and the slot order
  of `hashtable.ts`, recorded from TypeScript.

**P3b-lp** (`prove-smt`, module `lp`):
- In scope: `smt/solver/lp/` (14,502 lines) but `dependency.ts` (P3a).
- First: `numeric-pair`, `union-find`, `containers`, `lp-settings`, `nex`, `pdd`, then
  `lar-term`, `constraints`, `explanation`, `nex-creator`, `dep-intervals`, `pdd-solver`. Then the
  simplex core, `lar-solver`, `int-solver` with `hnf*` and `dioph-eq`, and the `nla-*` files.
- Last: `nra-solver.ts`, the one file that imports `nlsat` (its solver, algebraic numbers and
  types), which needs P3b-nlsat.
- First gate: `tests/unit/smt-intervals.test.ts` (16) and `smt-pdd.test.ts` (17).
- Oracle: `PROVE_IT_LP_TRACE=<dir>` makes each SMT decision write `<dir>/<digest>.lptrace`, the
  JSON lines of every call `theory-lra-*` makes into lp, with its arguments and result, every
  callback lp makes into the theory with its answer, and the theory's field reads of lp objects
  (`src/prover/smt/solver/lp-trace.ts` documents the format). `bun scripts/run.ts lp-trace`
  records them for the SMT inputs of the decider corpus in `tests/conformance/.lp-traces/<prover>`, and
  checks that each traced answer, statistics included, is the recorded one. A Rust replayer
  drives the Rust lp with the same calls, answers its callbacks from the trace and compares the
  rest.

**P3b-nlsat** (`prove-smt`, module `nlsat`):
- In scope: `smt/solver/nlsat/` (7,875 lines).
- First: `mpbq`, `upolynomial`, `upolynomial-factorization`, then `polynomial`, `algebraic`,
  `types`, then `atoms`, `interval-set`, `levelwise`, `evaluator`, `explain`, `solver`.
- It needs only P3a: from `lp` it takes `dependency.ts` alone.
- First gate: `tests/unit/smt-nlsat.test.ts`, all but the `nra …` groups (those wait for
  `nra-solver`, P3b-lp's last file).
- Status: ported, one `.rs` per TS file under `smt/src/nlsat/`; every non-`nra` group of
  `smt-nlsat.test.ts` passes as Rust tests that read the same fixtures
  (`tests/fixtures/nlsat/*.json`, through `nlsat/test_util.rs`). Representation: monomials are
  ids into the manager's table, which `rename` rewrites in place as the TS does; a `Polynomial`
  is an `Rc` node whose term order sits in a `RefCell`, since `lex_sort` and
  `make_first_maximal` reorder shared polynomials; an `Anum` is a shared `Rc<RefCell>` handle,
  since refinement changes it in place; atoms and clauses are `Rc`s with their mutable fields in
  `Cell`s. No module stores another's state: the solver owns the managers, the cache, the atom
  table and the assignment and passes them into each call; the atom table's `BoolVarHooks`
  (`on_mk`, `on_delete`, `bvalues`) reach the solver's per-variable vectors, from `Explain` too.
  TS throws are `Err(SmtError::…)`; `AddAllCoeffsRestart` is an internal error variant of
  `explain`. The `ResourceLimit` is passed to `check`/`check_assignment`, not stored. Next:
  `nra-solver` (P3b-lp) on top of it, then the decider differential once `core` calls `lp`.

**P3c SMT core** (`prove-smt`, modules `util` from P3a and `core`):
- In scope: `smt/solver/*.ts` (23,254 lines) but P3a's files; the `theory-lra-*` files (2,141)
  last, as they call `lp`.
- First, after P3a: `literal`, `sort`, `enode`, `case-split-queue`, `flat-literals`, then
  `ast.ts` (1,316: the hash-consed DAG), `clause`, `cg-table`, `sticky-generations`. Then the
  rewriters (`rewriter-tpl` and the files under it), `smtlib-parser`, `asserted-formulas`, the
  tactics, `relevancy`, `conflict-resolution`, the MAM and `e-matching`, the model files,
  `internalizer`, `context` and `solver`.
- First gate: `tests/unit/smt-clause-store.test.ts` (4) and `smt.test.ts` (24, inputs under
  `tests/fixtures/smt`). The decider differential on inputs without arithmetic atoms can run
  before P3b lands; the rest, once `theory-lra-*` can call `lp`.
- `decide` declines what the port does not reach yet, never guesses.

**P4 Isabelle** (`prove-isabelle`):
- In scope: `isabelle/` (11,713 lines) but `encode.ts`, plus the logic data (3.9: a binary second
  output of `scripts/isabelle-logic.ts`, `include_bytes!`, decoded once).
- P4a is `pure/` (6,628). First: `term`, `name`, `seq`, `table`, `list`, `interrupt`, then
  `type`, `logic`, `net`, `term-ord`, `consts`, then `envir`, `pattern`, `unify` and `thm` (the
  kernel).
- P4b is `provers/`, `tools/`, `isar/`, `tla/`, then `decide.ts`.
- First gate: `tests/unit/isabelle.test.ts` (5, theories under `tests/fixtures/isabelle`). The
  kernel has no TS unit tests of its own, so P4a adds Rust tests of `term`, `pattern`, `unify` and
  `thm` from Isabelle's behaviour on the fixture theories.

**P5b/c obligations** (`prove-obligations`), after P5a lands in `tla-front`:
- In scope: `src/obligations/` (8,873 lines; `format.ts` and `action.ts`'s `getHash` are LGPL)
  with `regroup.ts`, then `prep/` (2,202), the encoders (`smt/*.ts` 2,676, `zenon/encode.ts`,
  `isabelle/encode.ts`, `ptl/encode.ts`), `first-order.ts`, `ocaml.ts` and `tlaps-module.ts`.
- First: `format`, `pragma`, `expression`, then `equality`, `levels`, `operators`, `proof`,
  `substitution`, `temporal`, `tuples`, then `module`, `printer`, `regroup`, `subexpression`, then
  `source` (from `tla-front`'s AST), `anonymize`, `generate`, `normalize`, `simplify`, `action`,
  `index`.
- First gate: `tests/unit/obligations.test.ts`, `obligation-zenon.test.ts`,
  `obligation-isabelle.test.ts`.
- Then the encoder differential (2.2, layer 4), which the track builds: every corpus obligation's
  printed text, location, kind, fingerprint and every encoder's text, byte for byte against
  TypeScript.
- It needs no decider; it must not change what `decide` receives.

### 4c. P6, the driver

The design of P6, which the lead takes, and which the P5 session joins for the CLI once P5c is in.
It moves `prove.ts`'s driver to `prove-it-prover` while some back ends are still TypeScript, so
the boundary has to carry decisions both ways.

**Why not obligations and texts up front.** The SMT encoder numbers the CASE errors it
standardizes across the run (`getSession`). An obligation's count depends on every earlier
obligation that reached the SMT encoder, which depends on what earlier methods decided and on
fingerprint reuse. So texts cannot be computed before deciding, and the driver, not the encoders,
is what must move.

**Request and retry, as `Sources` does.** One host export, run in Rust:

```
prove(mains, known, options)
  → { kind: "proved", modules, reports, warnings }       every obligation settled
  | { kind: "needed", keys, texts, reports, warnings }   decisions Rust can't make yet
  | { kind: "error", name, ... }                         as getObligations throws today
```

- `known` holds the module texts under P5's keys (`tlapm:<name>`, `text:<path>`), and the answers
  of earlier rounds under `decide:<prover>/<digest>`: `{verdict, statistics, timeUsedMs}` or
  `{error}` (a `TlaProverError`'s message).
- The driver runs `prove.ts`'s algorithm: methods in turn, `Prep.already_processed` reuse by
  fingerprint, triviality, the CASE session, the reasons. It decides with every Rust back end
  that decides by default, on std threads (3.7).
- Where an obligation needs a back end that is still TypeScript and the answer isn't in
  `known`, the obligation waits, and its key goes into `keys`, with the text in `texts`.
- `reports` are the settled obligations, in order, so that `onObligation` streams as today.
  `warnings` are what `index::get_obligations` gave its warning sink, for `onWarning`.
- An error carries its name, `TlaProofError` or `TlaSyntaxError`, since `get_obligations` can
  throw either.
- JavaScript decides every needed key in the existing pool, in parallel, and calls again with
  the answers added.
- The driver runs again from the start. It is deterministic, so the same obligations settle the
  same way and the new answers let more of them go on.

**Rounds.** Each round settles every decision that is ready, so the number of rounds is the
longest chain of dependent TypeScript decisions: an obligation's methods tried in turn, and an
obligation that waits for an earlier one with the same fingerprint or for every earlier one to
learn its CASE count. The end-to-end differential reports the rounds per module, and if a chain
is long, the CASE wait is the place to cut it: it only waits on obligations whose encoding has
an incomplete CASE.

**One thread for Prep, the pool for deciding.** The front end's IR is `Rc`, so the obligations,
Prep and the encoders (P5c's `ship::encode_for_backend`, which takes the CASE count in its
`EncodingSession` and leaves the count after it) stay on the driver's thread, in obligation
order, as in the TypeScript, where they are about 9% of the time. Only the texts, which are
`String`s, go to the Rust back ends' threads and to JavaScript.

**Prep's order.** Prep keeps module-level caches, as the TypeScript does. All are memoisation
but temporal's `constantBodies`, which is keyed by a body alone: the first scope a shared body is
judged in decides it for every later one, even across modules. So an obligation's Prep result
depends on which obligations ran Prep before it in the process. The driver clears these caches
(P5c's `reset_caches`) at the start of each `prove` call and runs Prep in obligation order, which
makes a run reproducible. The end-to-end differential also runs each module once in a fresh
process, to show whether the TypeScript's carry-over between modules ever changes an answer.

**Cost of running again.** A cache keyed by the digest of `mains` and `known`'s module texts
keeps the parsed modules and the obligations, thread-local to the driver's thread, and every
encoder text by (obligation, method, CASE count), process-wide. The texts are filled in the
first round, whose Prep ran in a fresh run's order, so they are the texts a fresh run makes. A
round then costs the driver's bookkeeping, not Prep's 520 seconds. The cache changes no result,
and the differential runs once with it cleared each round.

**Time and cancellation.** `timeUsedMs` comes from whichever side decided, and the reason
`timeout` or `false` is computed from it as now. An abort stops JavaScript from calling again,
and the cancel cell stops the Rust decisions in flight.

**Selection.** `PROVE_IT_PROVER_DRIVER=ts|rust` picks the driver. The default stays TypeScript
until the end-to-end differential (2.2, layer 5) is clean on all 304 modules with 1 and 4
threads: identical `ProofObligation`s less `timeUsedMs`, and identical `missingProofCount` and
`omittedProofCount`.

**Stages.**
- P6a, the driver: `prove-it-prover::prove`, the host export, the loop in `prove.ts`, and the
  end-to-end differential.
- P6b, tlapm's state: `.tlacache` through OCaml's Marshal (`tlapm/cache.ts`,
  `ocaml-marshal.ts`, LGPL), and the JS CLI's `prove-it tlapm` on the Rust driver, compared
  with `conformance:tlapm` and the end-to-end differential with and without a cache, `--nofp`
  and `--nofpl`.
- P6c, the native binary's `prove-it tlapm`: it cannot call TypeScript, so it declines, as it
  does today, while any obligation needs a back end that is not yet Rust, and becomes native
  once all four are.

---

## 5. Expected speed

Correctness of verdicts comes first; speed is measured, not targeted, until P6.

### 5.1 Where the TypeScript's time goes

The split of 2.4: deciding 91%, Prep and encoding 8.5%, generating obligations 0.5%. CPU
profiles under Node (`--cpu-prof`, self time by source file through the bundle's module
markers), on three modules chosen for their mix of back ends, *measured*:

| Module (Node wall time) | Profile |
|---|---|
| `EWD998PCal_proof` (18 s; 468 SMT proofs) | Z3 core 42% (`ast.ts` hash-consing 6%, `rewriter-tpl` 5%, `internalizer` 4%, `context` 3%, `rewriter` 2%, `var-subst` 2%, the SMT-LIB parser 2%); obligations 20% (`expression.ts` maps and visitors 11%, `substitution.ts` 4%); the SMT encoder 7%; Prep 2.5%; garbage collection 15%; idle 7% |
| `FiniteSetTheorems_proofs` (19 s; SMT 141, Zenon 54, Isabelle 12) | Zenon 30% (`expr.ts` interning 8%, equality rules 5%, the index 3%); Isabelle Pure 16% (`term.ts` 4.5%, `thm.ts` 2%); Z3 core 13%; obligations 9%; garbage collection 22% |
| `AtomicBakeryWithoutSMT` (33 s; Zenon 115, Isabelle 14) | Zenon 54% (`expr.ts` 18%, equality rules 7%, `index-table` 6%, TLA rewrites 4%, OCaml's `Hashtbl.hash` 4%); Isabelle 12%; garbage collection 24% |

Three things stand out. Building and hashing hash-consed terms (Zenon's `expr.ts`, Z3's
`ast.ts`, Isabelle's `term.ts`) is the largest single cost in every back end. Garbage collection
takes 15–24% of all time, since every term, literal and clause is a heap object. And 7% of an
SMT-heavy module is idle: `proveObligations` yields to the event loop with `setTimeout` after
every report (the `// HACK` in `prove.ts`, so an abort can land), which costs at least a
millisecond per obligation; about 30 s over the corpus. That last one is a TypeScript fix
(`setImmediate`, or yielding only when a signal is set) that P0 can make without changing any
result.

Under Bun the prover is slower than under Node: 1.4–2.5× on the three modules (2.4), the most on
the SMT-heavy one. `scripts/run.ts` cites about 85 times on the SMT solver; that is not what these
modules show, and is worth re-measuring on the inputs it came from, since it is why the conformance
scripts run under Node. This matters for users, because a library user on Bun runs the prover on
JavaScriptCore, and there it loses proofs at the limits that Node finds.

### 5.2 What Rust changes

- **The same algorithms, about 2× on CPU-bound code.** DESIGN's measurements of the engine's
  ports (interning, hash-table probes) gave 1.7–2× over Bun for the same algorithm, and the
  prover's hot paths are the same kind of code: interning terms, probing hash tables, walking
  trees. Against Node the factor is smaller on tight loops V8 compiles well, and larger where
  the profile shows allocation.
- **No garbage collector.** Per-check arenas (3.3) free a whole decision at once; the 15–24%
  goes, and with it the heap ceiling that kills processes today (2.4).
- **No runtime dependence.** The same code under Node, Bun and the native binary, and the same
  results; the browser runs it as WebAssembly, whose cost against native code nobody has measured
  here yet (P1 measures it on PTL and P2 on Zenon). The Node–Bun gap of 2.4, and the proofs it
  loses at the limits, disappear.
- **Threads.** Today the decide pool parallelises decisions, but Prep and encoding (520 s, 8.5%)
  run on the main thread, one obligation after another. In Rust they run on the pool too,
  ordered only where the CASE-error numbering and fingerprint reuse require (3.7).
- **What it cannot change: the limits.** A decision that ends `unknown` at tlapm's limit takes
  the limit, in any language. Only proving it first saves time, and that changes the result:
  once Rust is the default, it may prove obligations TypeScript did not within the limit. That
  is allowed (tlapm's limits are wall clock and machines differ) but it is a visible change, so
  each flip reports how many obligations a run on the corpus proves that the TypeScript run did
  not, and `conformance:prove` counts them as it counts `late` today.

### 5.3 Projection

Per-module wall time on one thread, from the second run of 2.4, *projected*:

| Part | TypeScript (Node) | Rust | Basis |
|---|---|---|---|
| Generating obligations | ≈27 s | 10–15 s | 2× on tree code |
| Prep and encoding | ≈535 s | 150–250 s | 2× plus no GC (5.1) |
| Successful decisions | 1,015 s | 350–500 s | 2× plus no GC |
| Decisions ending `unknown` | 4,071 s | about the same, less what Rust proves in time | tlapm's limits |
| **Total** | 5,649 s | ≈4,600–4,850 s | |

So about 1.2× end to end on one thread on this corpus, because 72% of the time is limits. On the
part that is not (proofs, Prep, generation: about 1,580 s) it is 2–3×, and Prep and generation
spread over threads in Rust. For a user, who mostly proves what is provable, that part is what
they wait for; the limits are tlapm's choice and stay. Users on Bun gain another 1.4–2.5×. The
P0 decider corpus measures every decision on both sides and the projection is redone before the
first flip.

---|---|---|---|
| Generating obligations | 27 s | 10–15 s | 2× on tree code |
| Prep and encoding | 520 s | 150–250 s | 2× plus no GC |
| Successful decisions | at most ≈2,000 s (2.4's upper bounds) | 700–1,000 s | 2× plus no GC |
| Decisions ending at a limit | at least ≈3,500 s | the same, less those Rust proves in time | fixed by tlapm's limits |
| **Total** | 6,102 s | ≈4,400–4,800 s | |

So about 1.3× end to end on one thread on this corpus, 2–3× on the part that is not waiting for
limits, more with threads for Prep, and 1.4–2.5× more again for users on Bun. The P0 decider corpus replaces the bounds with measured times per decision before
the first flip; the projection is redone then.

---

## Handoff

Kept current by whoever holds the next stage: what is built, what the differential reports, what
is next.

- Phase 1: this document (#211).
- P0, the harness (#218): the step counters and statistics of 2.3 and 4a; `prover-inputs.ts`,
  `prover-differential.ts` and the resumable journal; the `prover/` crates; the `decide` export
  (ABI 13); `PROVE_IT_PROVER`. The record, `tests/conformance/prover-inputs.json`, holds 12,025
  inputs from all 304 modules, taken on the 4-core container under Node with tlapm's time limits
  for the step limits:

  | Prover | Inputs | unsat | sat | unknown at the step limit | other unknown |
  |---|---|---|---|---|---|
  | `smt` | 10,320 | 10,051 | 13 | 256 | — |
  | `z3` | 56 | 52 | 1 | 3 | — |
  | `zenon` | 897 | 769 | — | 41 | 48 exhausted, 39 memory limit |
  | `isabelle` | 455 | 366 | — | 30 (`Interrupt`) | 59 |
  | `ls4` | 297 | 296 | 1 | — | — |

  None stopped for a runtime limit (`unstable`), and none threw. Decided again by the Rust under
  the recorded step limits and no time limit (`prover-differential --side rust`), all 12,025 give
  the recorded verdict and statistics, so the record reproduces.
  Recalibrated on the Rust decider (a692935, the 4-core container): the step limits were the
  TypeScript's steps in tlapm's time, which is gone with it, and the four fixes below move the
  search, so `prover-inputs --record` decided every module again on the native deciders. It was
  12,100 inputs, `smt` 9,986 / 13 / 319 / 2 and `zenon` 949 with 102 at the step limit; Zenon and
  Isabelle lose inputs that `smt` now proves first, and 36 Zenon inputs that stopped at the step
  limit reach Zenon's memory limit first under the native decider's higher step limits.
  Porting Z3's limit checks in nlsat's polynomial managers (z3-5.3.3) moved 10 `smt` inputs:
  7 that were unsat now reach their recorded step limit, and 3 at the step limit changed their
  statistics; they were re-recorded with `prover-differential --side ts --update`, which keeps
  each input's step limit.
- P1, PTL (#231): `prove-ptl` gives the reference LS4's verdict on the 26 formulas of
  `tests/conformance/ptl`, and on the 297 LS4 inputs of the record the TypeScript's verdict and
  step count on every one (297 same, 0 differs, declined or crash). Rust decides PTL by default.
- P2 Zenon (#227, flip in this entry's PR): `prove-zenon` ports all of `zenon/` but `encode.ts`,
  one module per TS file. `tests/zenon.rs` ports `zenon.test.ts` on its fixtures (the checker's
  tests are in `src/check.rs`); `scripts/zenon-fixtures.ts` records what the TypeScript decides on
  each fixture under a step limit into `tests/fixtures/zenon/decisions.txt`, which the Rust matches
  in verdict, steps, every statistic and the proof's digest. Malformed input is declined. On the
  949 Zenon inputs of the record, `prover-differential --side rust --prover zenon` gives 949 same,
  0 differs, unstable, declined or crash, through the addon and through WebAssembly; the TS unit
  tests pass with `PROVE_IT_PROVER_ZENON=rust`. Rust decides Zenon by default. Size, release builds
  on linux-x64-gnu from b736513 to fb96510: `prove-it-engine.node` 5,918,368 → 7,080,784 bytes,
  `prove-it-engine.wasm` 4,303,223 → 5,210,377, the `prove-it` binary 5,701,384, unchanged (it
  doesn't link the prover yet). Rust's Zenon peaks at 958 MB where the TypeScript's takes
  1,416 MB on the input that reaches the memory limit. `conformance:prove` with Zenon in Rust and
  in TypeScript: on every obligation both runs finished, the same status, but for two SMT
  obligations that sit at Z3's time limit and `LamportMutex_proofs.tla` #388, which Rust's Zenon
  proves inside tlapm's time limit and the TypeScript's doesn't. Its input
  (`zenon/afc234afa4fc2a0a`) is `unknown` on both sides at the recorded step limit and `unsat` on
  both with no limit, in the same 94,929 steps and the same statistics and proof. On the 4-core
  container both runs lose a few large modules (`tcp_proof`, `BPConProof`, `CRDT_proof`) whose
  workers the container's memory limit kills; alone, `CRDT_proof` gives the same statuses both
  ways.
- P2 Zenon, the TypeScript deleted (ahead of P7, by the coordinator's decision): `src/prover/
  zenon/` is gone but `encode.ts`, which P5c owns, with `tests/unit/zenon.test.ts`,
  `scripts/zenon-fixtures.ts` and `TlaZenonError`. What the TypeScript decided stays as recorded
  expectations the Rust is tested against: the 949 Zenon inputs of `tests/conformance/
  prover-inputs.json` (`prover-differential --side rust --prover zenon`) and the 103 fixture runs
  of `tests/fixtures/zenon/decisions.txt` (`crates/prover/zenon/tests/zenon.rs`), which nothing
  rewrites now; `deciders.test.ts` pins the TypeScript's answer on its Zenon input, through the
  addon and through WebAssembly. In `deciders.ts` a backend without a TypeScript decider is
  decided by its Rust port alone: `PROVE_IT_PROVER` doesn't switch it, an aborted signal answers
  `unknown`, an input the port can't read, or declines, is a `TlaProverError` (failed, as tlapm
  counts it; the Rust Zenon declines nothing now), and where no engine loads, the WebAssembly
  module included, `decide` throws `EngineUnavailableError`, as `check` does. `prover-inputs
  --record` and `prover-differential --side ts` and `--update` decide such a backend with its Rust
  port, say so, and label those results `decider: "rust"`. `conformance:zenon` compares the native
  Zenon with tlapm's recorded results and binary. The PTL and Isabelle deletions follow the same
  path.
- P1 PTL, the TypeScript deleted (by the coordinator's decision, after Zenon's): `src/prover/ptl/`
  is gone but `encode.ts`, which P5c owns. `tests/unit/ptl.test.ts` keeps the encoder's tests,
  whose inputs the Rust PTL decides now; its two tests of the decider alone have counterparts in
  `crates/prover/ptl/tests/ls4.rs`, which also pins the inputs of its other tests with the verdict
  and steps the TypeScript gave. What the TypeScript decided stays as recorded expectations: the
  297 LS4 inputs of `tests/conformance/prover-inputs.json` (`prover-differential --side rust
  --prover ls4`, 297 same through the addon and through WebAssembly), and `deciders.test.ts` pins
  its answer on its LS4 input (`unsat` in 5 steps). PTL is decided as Zenon is, by its Rust port
  alone; text that isn't LS4 input is a `TlaProverError` with the message the TypeScript's
  `TlaSyntaxError` gave, where the port used to decline it. `conformance:ptl` decides with the
  native PTL. `THIRD_PARTY_NOTICES.md` named no path of the deleted decider.
- P4 Isabelle, the TypeScript deleted (by the coordinator's decision, with PTL's): `src/prover/
  isabelle/` is gone but `encode.ts`, which P5c owns, with `tests/unit/isabelle.test.ts`, every
  case of which `crates/prover/isabelle/src/decide.rs` tests, and `TlaIsabelleError`. The scripts
  that read the TypeScript went with it, and what they wrote stays as frozen data:
  `scripts/isabelle-expectations.ts` recorded the crate's `testdata/`, which nothing rewrites now,
  and `scripts/isabelle-logic.ts`, with the `Export.thy` and `export.ML` it ran in tlapm's heap,
  checked the exported net keys against the TypeScript's `keyOfTerm` and wrote `logic-data.ts`,
  from which `data/logic.bin` and its digest were made. What the TypeScript decided stays as
  recorded expectations: the 478 Isabelle inputs of `tests/conformance/prover-inputs.json`
  (`prover-differential --side rust --prover isabelle`, 478 same through the addon and through
  WebAssembly), the 42 runs of `testdata/decide.txt`, and `deciders.test.ts`'s pin of its answer
  on its Isabelle input (`unsat` in 840 steps). Isabelle is decided as Zenon and PTL are, by its
  Rust port alone; a theory that isn't ASCII, or an exception that escapes the port, is a
  `TlaProverError`, where the port used to decline it. `conformance:isabelle` decides with the
  native Isabelle under tlapm's 30 s, which the port enforces, so it needs no worker.
  `THIRD_PARTY_NOTICES.md`'s Isabelle section names the crate in place of the TypeScript.
- P3 SMT, the TypeScript deleted (after the flip, f5b7bef, which made Rust decide `smt` and `z3`
  by default): `src/prover/smt/solver/` is gone, `lp/`, `nlsat/` and `lp-trace.ts` with it, but
  the encoders in `src/prover/smt/*.ts`, which P5c owns; so are its unit tests (`smt.test.ts`,
  `smt-clause-store`, `smt-intervals`, `smt-pdd`, `smt-nlsat`, which run as Rust tests case for
  case, and the lp trace's two), the scripts that read it (the `smt-*-tables.ts` and
  `smt-*-reference.ts` writers, `nlsat-differential.ts`, `lp-trace.ts`), the errors only it threw
  (`SmtParseError`, `SmtUnsupportedError`, `SmtCanceledError`, `SmtInvariantError`,
  `NlsatUnsupportedError`, `PddMemoryOutError`; none was exported), and in Rust the lp call
  trace (`lp::trace`, `lp::json`, `tests/lp_trace.rs`, `tests/lp_trace_diff.rs` and its fixture),
  which only replayed the TypeScript's traces. `smt` and `z3` are Rust-only by the rule above.
  What the TypeScript decided stays as recorded expectations: the 10,320 smt and 56 z3 inputs of
  `prover-inputs.json`, the tables under `crates/prover/{num,smt}/tests/tables` (each directory's
  `README.md` says which deleted script wrote which, at f5b7bef), `tests/fixtures/nlsat/
  differential.json`, and `deciders.test.ts`'s pin of the TypeScript's answer on its SMT input,
  as smt and as z3 (`unsat`, 14 instances, 4,626 steps, as `tables/decide.txt` has it).
  `conformance:smt` compares the native decider with tlapm's recorded Z3 verdicts. A deviation
  from Z3 (below) is now fixed in Rust alone, and the inputs it moves re-recorded with
  `prover-differential --side ts --update`, which decides smt and z3 with the Rust port.
  `prover-differential --side rust` gives 10,320 of 10,320 smt and 56 of 56 z3 inputs the same,
  through the addon and through WebAssembly, none differing, unstable, declined or crashed. Under
  WebAssembly, three workers, the most a worker's process held (its `VmHWM`, sampled every half
  second) was 844 MB over the smt inputs and 1,637 MB over the z3 ones, well inside wasm32's 4 GB.
- The TypeScript dispatch removed, with no TypeScript decider left: `deciders.ts` keeps
  `decide`, which calls the native engine and throws where it declines or no engine loads, and
  `isBackend`. `DECIDERS`, `hasTypeScriptDecider`, `RUST_BACKENDS`, `PROVE_IT_PROVER` and
  `PROVE_IT_PROVER_<NAME>`, `verdict.ts`'s step counter (`Steps`, `createSteps`,
  `isStepLimitReached`, `DecideOptions.steps` and `.statistics`), `useTypeScriptBackends` and
  `prover-differential`'s `--side` are gone. `prover-differential` decides with the native
  engine, and `--update` re-records from it.
- P3b-lp (`prove-smt` module `lp`): every file of `smt/solver/lp/` is ported, `nra-solver.ts`
  included, on top of the nlsat port. nlsat steps on the same `ResourceLimit` as in the
  TypeScript, `nla.limit`. The architecture, written at the top of `lar_solver.rs` and
  `nla_core.rs`, is as follows.
  - **Owners:** the theory owns `LarSolver` (which owns `CoreSolver`, which owns `LpSettings`),
    `IntSolver` and `NlaCore`.
  - **Back-pointers:** the TypeScript's back-pointers are borrowed views, `Lia { lia, lra }` and
    `Nla { core, lra, limit, is_relevant }`, built per call. The nla helper classes are state
    structs inside `NlaCore`, with associated functions that take the view.
  - **LarSolver's callbacks:** each TypeScript callback becomes owned state of `LarSolver`, an
    event buffer, or a plain parameter.
    - The Diophantine solver's hooks and their undo are `LarSolver::dio_hooks`, run where the
      callbacks fired.
    - The throttle's lemma signatures are `LarSolver::nla_throttle_seen`, undone on LarSolver's
      trail.
    - `onChangedBounds` is `changed_bounds_pending`, which NLA drains at the start of each entry
      point and after its own `find_feasible_solution`. The TypeScript callback only writes NLA
      state that only NLA reads, so this is equivalent.
    - `isCanceled` is a closure. The cross-nested search's `inc` and the PDD solver's cancel
      check are parameters, called at the TypeScript's points.
  - **Trails and identity:** closure trails are undo enums. Monics, nexes, PDD nodes and
    equations are indices into arenas.
  - **Tests:** the first gate passes: all 16 tests of `smt-intervals.test.ts` and all 17 of
    `smt-pdd.test.ts` run as Rust tests. The other modules have Rust tests whose expected
    values come from running the TypeScript on the same setups: lemma texts, LIA move sequences,
    statistics counters, and counts of `is_canceled` calls.
  - **The LP call trace:** `tests/lp_trace.rs` replays the TypeScript's traces (`lp-trace.ts`,
    `scripts/lp-trace.ts`) against the Rust lp, `LarSolver`, `BoundPropagator`, `IntSolver`,
    `NlaCore` and `nra` included. nlsat's `inc` calls are checked by count per call. On the
    45 `tests/fixtures/smt` inputs and 27 nonlinear ones, all 72 traces are the same, with none
    declined. On the decider corpus (`prover-inputs.json`, every one of its 10,376 smt and z3
    inputs, 117M trace lines in total) all 10,376 traces are the same. The TypeScript's traced
    answers all equal the record. Run with `bun scripts/run.ts lp-trace --jobs 4` in batches by
    `--filter smt/0` … `smt/f`, `z3/`, replaying and deleting each batch: the traces take 5.8 GB.
  - **The glue:** P3c's theory_lra, instrumented on a local branch to write the same trace, made
    the TypeScript's lp calls call for call on all 10,320 smt inputs of the corpus. That Rust
    recorder was not kept, as the TypeScript SMT goes after the flip.
- P5a tlapm parse mode: `tla-front`'s `Mode::Tlapm` and `parse_tlapm_module` (#226), held equal to
  `parseTlapmModule` by `front-differential.ts tlapm-ast` (2,367 of 2,367 corpus modules, every
  mutation), the other modes byte-identical to before.
- P5b obligations: `prove-obligations` ports all of `src/obligations/` on `tla-front`'s AST, one
  module per TS file, `regroup` included; `index.rs` is `getObligations`. `scripts/
  obligation-differential.ts` runs the TypeScript and `obligations-dump` (the crate's binary) on
  every module of `proofs.json` and compares each module's obligations (id, location, kind, method,
  printed text), summary, warnings in order and error: 304 of 304 match. Each module has unit tests
  whose expected values come from running the TypeScript under Bun. Ported ahead of P5c, with the
  same tests: `ocaml`, the SMT encoder (`smt/`), `first_order`, the Zenon and Isabelle encoders,
  `prep/{md5, methods, fingerprint, level_comparison, enabled_axioms, normalize}` and
  `tlaps_module`.
- P5c Prep and encoders: `prep/action`, the PTL encoder and `ship`, the encoding slice of
  `prove.ts`: `encode_normalized` (one backend's text for a sequent Prep has normalized),
  `encode_for_backend` (method selection and normalization first), `encode_proof_theory` (written
  proof by proof, so tcp_proof peaks at 5.1 GB where the TypeScript needs 12.5 GB) and
  `ProofAttempt`, the one record of a method's outcome P6 wraps. `reset_caches()` clears every
  module-level cache. `scripts/encoder-differential.ts` runs `obligations-dump --encode` and the
  TypeScript on every module of `proofs.json`: every method's text or error for every obligation
  matches on 304 of 304, with and without a reset between modules, and every text whose key is in
  `prover-inputs.json` is one the Rust writes. 79 recorded SMT inputs are not written, because
  their CASE-error numbers depend on which methods `prove` tried; the script lists them. Known: a
  `ContextMap` holds its keys weakly, but the prefix it maps a key to usually holds that key, so,
  unlike an ephemeron `WeakMap`, entries live until `reset_caches()`; P6 resets per `prove` call,
  which bounds memory by the run. Freeing them within a run is open.
- P6b part 1, tlapm's state: `prove-obligations::marshal` ports `ocaml-marshal.ts` (LGPL, in its
  own file and in the notices' OCaml section), and `prove-it-prover::tlapm_cache` ports
  `cache.ts`: `load_fingerprints`, `KnownResults::new`, `KnownResults::save`, and `save_history`.
  - **Caller-supplied inputs:** the caller passes in the package version string
    (`tla-ts <version>`) and the local time, since `std` has no time zone. The TypeScript reads
    both itself.
  - **Results:** each result keeps the field it was loaded from. That stands in for the
    TypeScript's maps keyed by object identity.
  - **Tests:** `tests/tlapm_cache.rs` ports `tlapm-cache.test.ts`. It also checks fixtures that
    `scripts/tlapm-cache-fixtures.ts` records from the TypeScript:
    - marshal round trips byte for byte, covering every code, the size boundaries and OCaml's
      sharing codes;
    - files `prove-it tlapm` wrote, with and without `--nofp`, which load and re-save to the same
      bytes as the TypeScript re-saves them;
    - every encoded result, re-encoded at its stored date and version.
  - **Next:** P6a/P6b part 2 wires it into the driver and the CLI.
- P6a, the driver (#315): `prove-it-prover::driver` and the host export `prove`, selected with
  `PROVE_IT_PROVER_DRIVER=rust`; the TypeScript driver stays the default.
  - **Rounds:** the driver asks JavaScript for each module read (`module:<name>#<n>`) and each
    decision (keyed by obligation, method, prover, limit and text), and proves again with the
    answers. A run's obligations, Prep and encodings stay on a long-lived thread, which takes
    tcp_proof from over two hours to 57 s.
  - **Ill-formed text:** the engine's strings can't hold a lone surrogate. Read as U+FFFD, as
    `get_text` reads it, two different strings become one and `"\uD800" = "\uDC00" BY SMT` is
    proved, so the host's `prove` declines a file name, source or module read that holds one
    (`TlaUnsupportedError`, "not native yet: … isn't well-formed UTF-16") before it decides
    anything. Both bindings hand it a string's UTF-16 units unchanged, so it sees every one.
    Winning these back takes carrying the units faithfully through the front end and the
    encoders. The driver gives way to the TypeScript on no text.
  - **Checks:** `scripts/prover-driver-differential.ts` gives 304 of 304 corpus modules the same
    under both drivers with decisions replayed from the record; `tests/unit/prove-driver.test.ts`
    holds the cases seven break-it rounds found.
  - **Open:** three inputs where the Rust encoders emulate a JavaScript engine's exception, and
    the TypeScript throws it, where both should do what tlapm does. They differ between the
    drivers until the next PR makes the Rust follow tlapm:
    - `\h`, `\o` and `\b` numerals in an SMT obligation (`BigInt` in `smt/rewrite.ts`);
    - numerals large enough to reach a string length limit in the Zenon and Isabelle encodings
      (`String.prototype.repeat`);
    - proof-step levels past 2^53, or 2^32 in WebAssembly, where the Rust reads a `usize`.
  - **Known TypeScript deviations**, where the Rust does what tlapm does:
    - an INSTANCE of a module inside its own instantiation overflows the TypeScript's stack (a
      RangeError), where tlapm and the Rust report tlapm's bug "Stack overflow" (#308);
    - a method pragma's string (`(*{ by (prover:"…") }*)`, and the old `(*{ by (isabelle "…")
      }*)`) is read with `JSON.parse` by `obligations/pragma.ts`, which decodes `\n` or `\uD800`
      and throws a SyntaxError, tlapm's bug, on an escape JSON lacks such as `\q`. tlapm's lexer
      keeps a string's contents as written (`alexer.mll` 173-197, then `E_parser.string_val`'s
      `Bstring`), so `"\uD800"` is the six characters `\uD800`, a prover so named is unknown
      ("Unknown prover: \uD800") and a tactic reaches Isabelle's theory as written. The Rust
      `pragma::read_string` does that.
  - **Open:** a TAB or a carriage return in a pragma's string still fails with the TypeScript's
    "SyntaxError: JSON Parse error: Unterminated string", where tlapm's lexer fails the module
    (a TAB anywhere fails it before any pragma is read). A backslash before U+2028 or U+2029
    still ends the pragma's match, as the TypeScript's regular expression does, where tlapm reads
    on.

### Deviations from Z3

Where a back end does what the tool it ports does not. The Rust mirrored the TypeScript, so that
the differential stayed exact; with the TypeScript SMT deleted, these are fixed in the Rust alone and
the inputs they move re-recorded from it. smt-core.md §4 lists the SMT core's and points here for
the evidence. Lines are as of
b1b794c, before the fix; Z3's are of the tag `z3-5.3.3`.

**The gate is tlapm's record; Z3 4.8.9 breaks ties.** tlapm's build pins and bundles Z3 4.8.9
(`deps/z3/Makefile` at ff40755) and runs it as `z3 -smt2 -v:0 AUTO_CONFIG=false smt.MBQI=true`
(`src/params.ml:230`). `proofs.json` was recorded with tlapm 5f5037f's release build on macOS
(the configuration `tlapm.json` keeps), whose `deps/z3/dune` installs that Z3 4.8.9
(`z3-4.8.9-x64-osx-10.14.6`) to `lib/tlapm/backends/bin`, first on the PATH tlapm runs it with.
On Simple's `Init => Inv` (`smt/5e53b781a834c8ec`, tlapm's `13e58ea1eeb4ae17`), which `proofs.json`
records as proved by tlapm's SMT, Z3 4.8.9's release binary answers `unsat` in 0.3 s, where Z3
5.3.3 times out at 5 s and 30 s. Over the 10,373 `smt` and `z3` inputs matched to tlapm's, 4.8.9 and tlapm's
record both prove 10,074, 4.8.9 alone 121 and tlapm alone 33; 5.3.3 disagrees with the record on
44, 4.8.9 on 154: the recording ran 4.8.9 on another machine under a 5 s wall-clock limit, so
an input near the limit can go either way, and the audit is read input by input. The audit below
was run against 5.3.3, and causes 1 and 4 were fixed toward it, which lost Simple's four
`Init => Inv` obligations.
Against Z3 4.8.9's source:

| Cause | Z3 4.8.9 | Now |
|---|---|---|
| 1. `flatten_clauses` | distributes `(or a (not d))` when `d` has one reference or `a` is a literal, with no count of occurrences (`smt/asserted_formulas.cpp:378-415`) | as 4.8.9 |
| 2. `false` in the model | `get_assignment` answers `l_false` for false (`smt/smt_context.cpp:1503-1510`) | as 4.8.9 and 5.3.3 |
| 3. a released rewriter's last result | `m_r` is declared last, so released first (`ast/rewriter/rewriter.h:221-223`) | as 4.8.9 and 5.3.3 |
| 4. `is_shared` | no cache: asks again each time (`smt/smt_context.cpp:4493-4560`) | as 4.8.9 |

The ported core is of a later generation than 4.8.9, which has no `dioph_eq`, `nla_grobner`,
`nla_throttle`, `nla_patcher` or `nla_divisions`, a 279-line `nra_solver.cpp` (1,108 in 5.3.3),
and fewer limit checks in the polynomial managers (`polynomial.cpp` 10 against 5.3.3's 18) and
nlsat (7 against 10). So the gate is tlapm's record, `proofs.json`: what tlapm proves, the port
must prove; Z3 4.8.9 decides between two searches where the port's loses an obligation tlapm
proves. A 4.8.9 audit is read input by input, not as a target of all same. The 5.3.3 audit below
stays as the record of that run.

The limit checks ported from 5.3.3's polynomial managers (#262) stay: of the 10 `smt` inputs they
moved, 7 belong to obligations tlapm proves with SMT (SumAndMax #28 and #30, AddTwo #14,
FiniteSetsExtTheorems_proofs #148 and #171, BagsTheorems_proofs #67, DiningPhilosophers_proof #14)
and 3 to ones it proves with Zenon (DiningPhilosophers_proof #33, #241 and #519), and on the record
recalibrated since, the port proves all 10 with tlapm's prover.

With causes 1 and 4 as 4.8.9 has them, the record was decided again (`prover-inputs --record`), and
each input whose search did not move, by `prover-differential` at the earlier limits, kept its
earlier entry, so a recalibration moves only the limits of searches that moved (247 kept, two of
them flips the clock alone made). Against tlapm's record, prove then proves 33,019 of the 33,025
obligations tlapm proves, against 33,016 before: Simple's four `Init => Inv` come back, and
Boulanger #240 (`smt/b2ca9ee96f3db516`) is lost. Its 4 distributions are the ones 4.8.9's source
makes, all of a disjunction with one reference, and Simple needs the same kind; without any, it is
`unsat` in 1,332,097 steps and Simple is not proved. The port's search after them takes 8,170,365
steps and 534,764 instances where it took 1,807,047 and 94,446, which places the divergence past
`flatten_clauses`, in the later generation of the solver. Z3 4.8.9 is itself near its limit
there: run as tlapm runs it with `-T:5` on a 4-core machine, it timed out once (rlimit 3,357,441)
and proved it once in 3.98 s with 162,971 instances (rlimit 4,021,756). It stays open.

- **A model's hold on a builtin declaration (`div0`, `mod0`, `/0`)** moves smt/0c812b0a8aa1347b,
  c0119d516427b279, f57d6baf800a11d6, 44fea97e4ee0312c and a50910e8b0798813 (all `unknown` at
  the step limit in the record).
  - *TypeScript.* theory_lra's divisions by zero are interpreted by the model
    (`model-generator.ts:26-31`, registered at `:91`). `ProtoModel.registerFunc` holds the
    declaration with `incDeclRef` (`proto-model.ts:267-275`); `unregisterDecl` (`:480-498`),
    `release` (`:511-524`) and `mkModel` (`:528-540`, which moves it to the new model) drop it with
    `decDeclRef`. The applications of `div0` count it under its signature (`ast.ts` `holdDecl`,
    `releaseDecl`, `:432-469`), but `incDeclRef` and `decDeclRef` (`:476-509`) count it in
    `declRefCounts` (`:303`), which holds only user declarations: `undefined++` is NaN and
    `NaN > 0` is false, so every drop deletes the declaration (`numDecls--`, its small id, `-1`
    from `Z3_SMALL_IDS` at `:340`, pushed on `freeSmallIds`) and the next hold makes it again with a
    new small id (`:489`), while its applications still hold it. `getNumAsts` (`:354-356`) counts
    `numDecls`. It seeds the Boolean `RandomGen` of every `ProtoModel` (`proto-model.ts:245`) and
    `getSomeValue`'s pick in a finite sort (`:336-342`), which model completion calls
    (`model-evaluator.ts:93,160,233-238`, `proto-model.ts:395,418`, `auf-solver.ts:499`) on the
    models MBQI checks.
  - *Rust.* `ast.rs` mirrors it with `decl_ref_counts: Vec<Option<i32>>` (`:429`, `None` is the
    NaN; `inc_decl_ref`, `dec_decl_ref`, `:751-811`; `get_num_asts`, `:551`), since 3e31515;
    `proto_model.rs` holds and drops as the TypeScript (`register_func` `:456-469`,
    `unregister_decl` `:822-843`, `release` `:862-879`, `mk_model` `:888-905`) and seeds from
    `get_num_asts` (`:389`, `:585`). Regression input `smt/tests/inputs/builtin-decl-release.smt`.
  - *Z3.* `arith_decl_plugin.cpp:423-425` makes `/0`, `div0` and `mod0` with
    `ast_manager::mk_func_decl` on each request, hash-consed to one `func_decl`
    (`ast.cpp:1963`, `register_node_core` `:1665-1674`); the plugin keeps no reference. That one node
    has one count, `ast::m_ref_count` (`ast.h:483,491-499`, `ast_manager::inc_ref`/`dec_ref`
    `ast.h:1705-1715`), which its applications (`ast.cpp:1714`, released at `:1823`) and models
    (`model_core::update_func_interp` `model_core.cpp:84-103`, `unregister_decl` `:106-130`,
    `~model_core` `:22-33`, `proto_model::mk_model` `proto_model.cpp:373-383`) share.
    `delete_node` (`ast.cpp:1778`) frees it and recycles its id (`:1795`, `id_gen.h:30-47`) only
    when the last of them goes, so a model dropping `div0` while an application holds it changes
    nothing. `get_num_asts` is `m_ast_table.size()` (`ast.h:1701`); it seeds `basic_factory`
    (`proto_model.cpp:35`, `value_factory.cpp:28-36`) and `user_sort_factory::get_some_value`
    (`value_factory.cpp:76-92`), which model completion reaches on the models
    `smt_model_checker` checks (`smt_model_checker.cpp:399-431`), whose divisions by zero theory_lra
    asks for (`theory_lra.cpp:4244-4251`, `smt_model_generator.cpp:412-450`).
  - *Verdicts.* It changes verdicts, not only statistics. A different number of ASTs seeds model
    completion differently, so MBQI checks other models and adds other instances, and the search
    under the step limit is another one, which can close in time where the other does not. On
    smt/0c812b0a8aa1347b (step limit 2,305,796) the TypeScript gives `unknown` at the limit
    (153,469 instances, 2,305,801 steps) and the Rust as it was before 3e31515, counting the
    declaration from 0, `unsat` (24,889 instances, 881,375 steps). It cannot make a verdict wrong:
    a model only chooses instances, and each instance is sound, so it moves inputs between
    `unknown` and a decided verdict. Counting from 0 is not Z3 either: a count of its own still
    releases the declaration when the model's last hold goes, while an application holds it.
  - *a50910e8b0798813* belongs here, though 3e31515 did not list it: the Rust before 3e31515 gives
    `unknown` with 131,956 instances and 3,307,788 steps, and with it the record, `unknown` with
    3,307,783 steps and no instances (the limit stopped a step that throws).
  - *Fixed* on both sides: `incDeclRef`/`inc_decl_ref` and `decDeclRef`/`dec_decl_ref` count a
    model's hold on a builtin declaration with a signature under that signature, with its
    applications, as Z3 counts the one `func_decl`; other builtin declarations, which Z3's plugins
    keep, are not counted (`smt-ast.test.ts`, `tests/ast.rs`). Decided again by the fixed
    TypeScript (`prover-differential --side ts --prover smt`), 10,316 of the 10,320 smt inputs give
    the record and four move, which the record must take with `prover-inputs --record`:

    | Input | Record | Fixed |
    |---|---|---|
    | smt/0c812b0a8aa1347b | `unknown` instances=153469 steps=2305801 | `unsat` instances=24889 steps=881375 |
    | smt/44fea97e4ee0312c | `unknown` instances=37134 steps=1629193 | `unknown` instances=65627 steps=1629192 |
    | smt/a50910e8b0798813 | `unknown` steps=3307783 | `unknown` instances=131956 steps=3307788 |
    | smt/c0119d516427b279 | `unknown` steps=2572033 | `unknown` instances=28904 steps=2572037 |

    smt/f57d6baf800a11d6 gives the record again. The fixed Rust gives the fixed TypeScript's answer
    on all 10,320, the four that move included. Of the tables, only `models.txt` moves: its `partial-theory` model, which
    interprets `div0`, now leaves the declaration to its application when it is released
    (`asts=181`, was 180). `tests/inputs/builtin-decl-release.smt` is replayed in `tests/smt.rs`,
    which pins the TypeScript's answer on it.
  - *Audit against Z3 5.3.3: neither side is Z3.* Z3 5.3.3 from PyPI (`z3-solver==5.3.3.0`), run as
    tlapm runs it (`-smt2 AUTO_CONFIG=false smt.MBQI=true`) with `rlimit` set to the record's step
    limit, and with `trace=true` to log its instances (each `[instance]` line, keyed through its
    `[new-match]` or `[inst-discovered] MBQI` line to the quantifier and binding ids). The
    TypeScript's instances were logged with the same Z3 ids (`AstManager.ids`) from
    `QiQueue.instantiateEntry`, before the fix (98b901c) and after (ea83e9c; HEAD, with
    b830769's nlsat steps, gives the same streams). At 200,000 steps both give Z3's first 1,214
    instances exactly.

    | Input | Z3 at the limit (instances, rlimit-count) | Before | Fixed | First instance off Z3 (before / fixed) |
    |---|---|---|---|---|
    | 0c812b0a8aa1347b | `unknown` 120,761, 2,306,586 | `unknown` 153,469 | `unsat` 24,889 | none / 1,255 |
    | a50910e8b0798813 | `unknown` 93,193, 3,308,327 | `unknown` ~62,900 | `unknown` 131,956 | 252 / 3,299 |
    | c0119d516427b279 | `unknown` 48,386, 2,572,601 | `unknown` ~31,600 | `unknown` 28,904 | 155 / 155 |
    | 44fea97e4ee0312c | `unknown` 60,308, 1,630,104 | `unknown` 37,134 | `unknown` 65,627 | 74 / 74 |

    Before the fix, the TypeScript makes all of Z3's instances on 0c812b0a8aa1347b (120,761 at
    the limit, and all 239,484 at `rlimit=4000000`), where the fix leaves Z3 at the 1,255th; on
    a50910e8b0798813 the fix keeps to Z3 longer (3,299 against 252). c0119d516427b279 and
    44fea97e4ee0312c leave Z3 at the same instance either way, by another deviation. Over the 77
    smt inputs with `div` or `mod`, at their limits, no other input tells the two apart. No count
    at the limit matches Z3's, for a deviation of its own: the TypeScript's steps run behind
    Z3's `rlimit-count` (on 0c812b0a8aa1347b it makes Z3's 120,761 instances and 32,708 more
    within the limit). Z3 does not prove 0c812b0a8aa1347b in 20 s (840,277 instances), so the
    fixed `unsat` is not Z3's answer.
  - *How it moves the search.* Not through `getNumAsts`: forcing every value it returns, or only
    the seeds of `ProtoModel`'s `RandomGen`, to the other side's sequence leaves each stream as
    it was. It moves the small ids: `freeSmallIds` is Z3's LIFO `id_gen` (`id_gen.h:30-47`), so
    when `div0` and `mod0` give back their ids decides which ids the aux context's next skolem,
    `poly` and numeral declarations get, and those order `propagate_values`
    (`asserted-formulas.ts` `isGreater`) and `rematch`. On 0c812b0a8aa1347b, forcing the one
    numeral declaration the fixed TypeScript makes after the 1,214th instance (id 490) to any id
    below 488 makes it follow Z3; the NaN gives it 480. The NaN is not Z3 either: it pushes the
    declaration's `funcDecls` small id, `-1`, on `freeSmallIds`, frees an id twice and hands out
    `-1`; it matches 0c812b0a8aa1347b by the order it happens to give.
  - *What Z3 does.* By its source the fix counts as Z3 does: the plugin makes `div0`, `mod0` and
    `/0` with `mk_func_decl` on each request (`arith_decl_plugin.cpp:423-425`), hash-consed to one
    node (`register_node_core`, `ast.cpp:1665-1691`), whose one `m_ref_count`
    (`ast.h:483-499,1705-1715`) its applications (`ast.cpp:1712-1714`) and models
    (`model_core.cpp:84-103`, released in `unregister_decl` `:106-130` and `~model_core`
    `:22-33`; `proto_model::mk_model` moves them, `proto_model.cpp:373-386`) share; the node
    leaves `m_ast_table` (so `get_num_asts`, `ast.h:1701`) and recycles its id
    (`RECYCLE_FREE_AST_INDICES`, `ast.h:55`, `ast.cpp:1792-1798`) only in `delete_node`, at the
    last `dec_ref`. But Z3's runs behave as if no model holds them when the model checker's aux
    scope is popped. The `div0` and `mod0` applications on 0c812b0a8aa1347b are the aux
    context's (theory_lra's `found_underspecified`, `theory_lra.cpp:304-334`), released by the
    pop at the end of `model_checker::check(q)` (`scoped_ctx_push`,
    `smt_model_checker.cpp:361-433`). The TypeScript's aux context still holds the model of the
    last restricted counterexample there (the loop stopped at `m_max_cexs`), and gives the
    declarations back at the next `search`'s `reset_model` (`smt_context.cpp:4038`), after the
    next quantifier's skolems and `poly` assumption. Releasing that model before the pop
    (`Context.resetModel` before `pop`, with the fixed counting), or not counting a model's hold
    on these declarations at all, gives Z3's stream on every input above: all 239,484 on
    0c812b0a8aa1347b and 3,299 on a50910e8b0798813. Z3's source, as read
    (`smt_model_checker.cpp:378-433`, `smt_context.cpp:3836-3880,4024-4038,4940-5016,3183-3188`),
    keeps `m_model` until that `reset_model` too, so where Z3 lets the model go is not found
    yet; an instrumented Z3 (printing `get_num_asts` and the declarations' ids and counts at
    `model_core`'s holds and drops) would settle it.
  - *Status: reverted, open.* The fix (ea83e9c) and its re-recording (9621162) are reverted:
    on smt/0c812b0a8aa1347b it leaves Z3's stream at the 1,255th instance and proves what Z3 does
    not, while main's TypeScript makes all of Z3's instances there, and a change of ours must not
    put a verdict Z3 doesn't give into the record. So the TypeScript keeps its NaN count, the Rust
    mirrors it (`decl_ref_counts: Vec<Option<i32>>`, 3e31515), and the record is main's. Neither is
    Z3; the change that matches Z3's runs on every input that tells them apart (the fixed counting
    plus releasing the aux context's model when the model checker pops its scope) waits for the
    line in Z3 that releases that model, which an instrumented Z3 would show. It is then made on
    both sides with `prover-differential --side ts --update`.

The record holds what the decider answers (the TypeScript until a692935, the Rust since), so it
cannot show where the decider leaves Z3.
`scripts/z3-parity.ts` runs Z3 4.8.9, the version tlapm bundles, or with `--version 5.3.3` that
one, on every `smt` and `z3` input of the record as tlapm runs it:
`z3 -smt2 -v:0 AUTO_CONFIG=false smt.MBQI=true`, under the time limit prove sent the input with
(5 s for all but 24 inputs; 2 have an `rlimit` budget and no time limit), which prover-inputs now
writes to `.prover-inputs/time-limits.json`. The script's header cites tlapm's source for each part
of the invocation. It fails unless the binary is the pinned one of its version by SHA-256 (4.8.9's
`4321b0c0…1436`, of the `z3-4.8.9-x64-ubuntu-16.04` release; 5.3.3's `f6aa070c…6470`, of the
`z3-solver` 5.3.3.0 wheel), journals each run, and writes `.z3-parity-<version>.json`.
`parity-compare.ts` joins a 4.8.9 audit with tlapm's verdicts in `proofs.json`, the record, the
record of another commit and a 5.3.3 audit. The runs below were of Z3 5.3.3.

On the TypeScript's record of `main` at b830769, and on the record recalibrated on the Rust decider
with causes 1 to 4 below fixed (a692935):

| | `smt` at b830769 | `z3` | `smt` at a692935 | `z3` |
|---|---|---|---|---|
| Same verdict | 10,246 | 54 | 10,317 | 56 |
| The decider proves, Z3 doesn't | 4 | — | 1 | — |
| Z3 proves, the decider doesn't | 70 | 2 | 2 | — |
| A verdict that contradicts (`sat` against `unsat`) | 0 | 0 | 0 | 0 |
| Z3 errors | 0 | 0 | 0 | 0 |

Where both prove, the search is mostly Z3's: on 9,996 of the 10,032 inputs both prove, the
TypeScript makes as many quantifier instances as Z3. Its step count is not Z3's `rlimit-count`,
though (equal on 1,464 inputs, a median of 0.92 of it): some of Z3's resource-limit charges are not
counted. At a692935, 10,099 of the 10,102 inputs both prove make Z3's number of instances; the
other three (`3d0e1c6148767e0b`, `6c6369c50591f209`, `aa5d456f2b65d6eb`) made the same counts
before the fixes.

How the divergences were found: the instance streams. `smt.qi.profile_freq=1` makes Z3 print each
instance's quantifier as it makes it, and the TypeScript's `QiQueue.instantiateEntry` gives the same
stream. Z3 names a quantifier without `:qid` `k!<line>` with a numerical qid, and compares two
quantifiers' qids unless both are numerical (`ast.cpp:448-449`), so a `:qid k!<line>` written into
the text can stop Z3 from sharing two equal quantifiers and change its search (it does on
`beb7dd1741444a77`). Z3's streams therefore come from the text as recorded, and the TypeScript's
from the text with the names written in, which it does not change, since the TypeScript never
compares qids (`ast.ts:1063`). Z3's `trace=true` changes Z3's search and cannot be used. A Z3 5.3.3
built from the tag with tracing (`Z3_ENABLE_TRACING_FOR_NON_DEBUG`) gives the pinned binary's
counts. Its `qi_queue_profile`, `mam_candidate` and `trigger_bug` traces leave the search
unchanged, but `model_checker` changes it.

Where the instance streams part, finer streams of both, compared event by event, place the first
event that differs. In the build, trace points that print terms with `mk_ll_pp` (they leave the
counts unchanged) give the e-matching candidates and code-tree runs, the matches and their
fingerprints, the instantiation attempts with their bindings, the MBQI counterexamples and
inverses, the auxiliary context's assertions, preprocessed formulas and decisions, the model
finder's partial functions, the fresh names, and the merges. Hooks on the same functions of the
TypeScript give its stream. A cause is confirmed by adding Z3's behaviour to a scratch copy of the
TypeScript: the instance stream must then be Z3's past the old first difference.

**The TypeScript proves, Z3 doesn't.** Z3 times out at 5 s and at 50 s on each.

| Input | Obligation (`proofs.json`) | First instance that differs | Is the TypeScript's `unsat` right? |
|---|---|---|---|
| `smt/8df9b72d29f8a626` | VoteProof `Consensus` #33 | 37th: Z3 `k!33` (`SeqLenDef`, which has no pattern), the TypeScript `k!35` | Yes. Z3 5.3.3 proves it with `smt.random_seed` 1, 2 and 3, and with its default configuration. tlapm's Isabelle proved the obligation. |
| `smt/fe8845daad4c648e` | `EmptySetEqCases_proofs` #1084 | 53rd: Z3 makes one more `k!25` (`EnumDefIntro 1`) | Yes. Z3 proves it with seeds 1, 2 and 3. tlapm's Z3 proved it. |
| `smt/5e53b781a834c8ec` | TeachingConcurrency `Simple` #7, #27; `Simple_proof` #7 | 163rd: Z3 `k!39`, the TypeScript `k!42` | Yes. Z3 proves it in 1.1 s with its default configuration. tlapm's Z3 proved it. |
| `smt/1319a2956705afce` | `EmptySetEqCases_proofs` #640 | 371st: Z3 `k!28`, the TypeScript `k!25` | Yes, from the obligation: tlapm's Zenon proved it. No Z3 setting tried proves the text: seeds 0 to 14 with tlapm's options and 0 to 13 with the default configuration, at 60 s each. |
| `smt/0c812b0a8aa1347b` (after part 3) | DiningPhilosophers `DiningPhilosophers_proof` #274 | none on `main`: its 153,469 instances are Z3's first 153,469 | Yes, from the obligation: tlapm's Isabelle proved it. Z3 doesn't decide the text at 5 s or 50 s, or with seeds 1 to 3 or the default configuration at 60 s. |

So none of the five is a soundness risk: each `unsat` holds. They are divergences in the search.
Each run's instances are Z3's up to the point in the table. After that, the TypeScript happens to
reach a proof, and Z3, on its own path, doesn't in the time.

**Z3 proves, the TypeScript doesn't: 72.** Each was decided again by the TypeScript with no time
limit and a step limit of twice Z3's `rlimit-count`.

- **64 come from the step limits** (62 `smt`, both `z3`). The TypeScript proves each with exactly
  Z3's number of instances, so it makes the same search. It needs about 0.9 of Z3's
  `rlimit-count`, and the record's step limit is less than that.
  - The record's step limit is the steps the TypeScript took in tlapm's time on the recording
    machine. That is 0.08 to 0.88 of the resources Z3 uses in that time.
  - These are a matter of the decider's speed, not of the search.
- **8 are real divergences** (all `smt`). The first instance that differs, Z3's against the
  TypeScript's:
  - `cb7b13d3236da8ea` 413th, `k!41` against `k!30`; Z3 proves it with 0.14 of the record's
    step limit.
  - `ee2307985b84e424` 137th, `k!43` against `k!38`; Z3 proves it with 0.22 of the step limit.
  - `52c873767bacfb3b` 2,343rd, Z3's last instance, the goal's `k!270`, against `k!23`.
  - `024f5dc53f8b63a5` 214th, `k!25` against `k!431`.
  - `d542f926ff5ed013` 213th, `k!282` against `k!276`.
  - `fa51a87ba4ebf399` 7,702nd, `k!284` against `k!286`.
  - `41a69bf765dd7c8b` 11,110th, `k!197` against `k!53`, and `beb7dd1741444a77` 52,974th, `k!33`
    against `k!49` (the 152nd with the names written in, which change Z3's search there). The
    TypeScript still proves these two with more steps, on another path.

**Where the searches part.** Four causes, in the TypeScript and in Z3 5.3.3 (paths under
`src/prover/smt/solver/` and Z3's `src/`):

1. **`flatten_clauses` distributes a shared conjunction.** `cb7b13d3236da8ea`,
   `ee2307985b84e424`, `52c873767bacfb3b`, `024f5dc53f8b63a5`, `d542f926ff5ed013`,
   `fa51a87ba4ebf399` and `beb7dd1741444a77`; and of the TypeScript's proofs `fe8845daad4c648e`,
   `5e53b781a834c8ec` and the first divergence of `1319a2956705afce`.
   - Z3 distributes `(or a (not d))` into clauses only when the disjunction `d` has no other
     parent, `d->get_ref_count() == 1` in `can_distribute` (`solver/assertions/asserted_formulas.cpp:433-437`,
     in `flatten_clauses`, 411). `asserted-formulas.ts:426-430`, in `flattenClauses` (405-468),
     checks only the occurrence count, so it also distributes a `d` that another formula holds.
   - The difference shows in MBQI's auxiliary context, which preprocesses each check's formulas.
     On `cb7b13d3236da8ea` the events agree up to the 589th instantiation attempt, an MBQI
     instance of `k!28`. In the check of `k!26` before it the auxiliary context's assertions are
     the same, but after `flatten_clauses` its clauses differ (`(not (or …))` over a disjunction
     that also occurs elsewhere). Its decision at level 4 then differs, and so does its
     counterexample for `k!28` (`smt_model_checker.cpp:218`, `add_instance`, against
     `model-checker.ts:200`). On `ee2307985b84e424` the first difference is again a preprocessed
     clause of the auxiliary context.
   - With the reference-count condition added, the TypeScript's instance stream is Z3's to the
     end on `cb7b13d3236da8ea` (471 instances), `ee2307985b84e424` (1,257), `52c873767bacfb3b`
     (2,343), `024f5dc53f8b63a5` (1,045), `d542f926ff5ed013` (53,000) and `fa51a87ba4ebf399`
     (8,000), and it proves each. On `beb7dd1741444a77` it is Z3's for all 449,825 instances Z3
     makes in 6 s, and the TypeScript proves it. On `fe8845daad4c648e` (28,303) and
     `5e53b781a834c8ec` (86,967) it is Z3's whole 5 s stream, and the TypeScript no longer proves
     either within its step limit.
2. **The model gives `false` the value `true`.** `8df9b72d29f8a626`.
   - Z3's model generator takes a Boolean class's value from `get_assignment(enode)`, which
     answers `l_false` for the `false` node (`smt/smt_model_generator.cpp:102`,
     `smt/smt_context.cpp:1681-1690`), and `get_assignment(expr)` answers `l_false` for `false`
     before it looks at a Boolean variable (`smt_context.cpp:1646-1648`). The TypeScript's
     `model-generator.ts:61` calls `findAssignment` (`internalizer.ts:380`), which reads the
     variable that `false` shares with `true` (209) before it checks for `false` (389-390), and so
     answers true.
   - So `(Cast_Bool false)` has no entry of its own. MBQI's `cleanup_instantiation_sets`
     evaluates it with model completion and gives `Cast_Bool` an else value
     (`model-evaluator.ts:225`, `getMacro`, against `model/model_evaluator.cpp:394`). In Z3 the
     function stays partial, so `complete_partial_funcs` gives it a projection and the fresh
     `Cast_Bool!17` (`smt_model_finder.cpp:955-971, 1072-1109`, against `auf-solver.ts:466-481,
     520-542`). The fresh names, the auxiliary context's clauses and the counterexamples part from
     there, and the 37th instance, made by MBQI, differs.
   - With `false` answered first, the TypeScript's stream is Z3's for all 9,343 instances it
     makes within its step limit, and it no longer proves the input. This corrects the guess that
     the model checker itself parts.
3. **A released rewriter keeps its last result.** The second divergence of `1319a2956705afce`,
   at the 736th instance once the first two causes are taken away.
   - The auxiliary context gets the same restriction `(or (= k!269 v45) (= k!269 v19) …)`
     (`smt_model_finder.cpp:2674`, `restrict_sks_to_inst_set`). The first pass of
     `propagate_values` (`solver/assertions/asserted_formulas.cpp:618-622`, against
     `asserted-formulas.ts:351-359`) sorts its disjuncts by expression id on both sides
     (`ast/rewriter/bool_rewriter.cpp:274-277` with the `ast_lt` of `ast/ast_lt.h:30-32`, against
     `rewriter.ts:454`). The eight disjuncts that move to the front have recycled ids, and those
     differ.
   - The two managers give and free the same ids for 52,729 creations and deletions. The first
     difference is the release of a model's evaluator after an MBQI check: Z3 frees a
     `(not (= …))` that the evaluator's last result held, and the TypeScript never frees it.
     `~rewriter_tpl` releases its member `m_r` (`ast/rewriter/rewriter.h:227`) before the
     shifters and the caches (`rewriter.cpp:201-203`). `RewriterEngine.release` and
     `BetaReducer.release` (`rewriter-tpl.ts:420-424, 926-929`) release the shifters and the
     caches but not `lastResult`, and so do `rewriter_tpl.rs:833-837, 1489-1492`.
   - With `setLastResult(-1)` first in both, the ids agree for all 192,132 creations and deletions
     the TypeScript makes in 400,000 steps, and its instance stream is Z3's for all 285,514
     instances Z3 makes in 5 s.
4. **A stale `is_shared` cache.** `41a69bf765dd7c8b`, which the first three causes don't touch.
   - The ids agree up to the 11,110th instance, and the assignments and merges until a final
     check's model-based theory combination (`smt/theory_lra.cpp:1741-1779`, `assume_eqs`,
     against `theory-lra-model.ts:75-113`). Z3 counts `(Proj_Int (y1!6 (FunApp (e!7 …) …)))`, a
     chain of four `y1!6`, as relevant and shared and assumes it equal to a `Proj_Int` term of the
     same value. The TypeScript counts it as not shared and assumes `(Proj_Int (y1!6 (z!0 …)))`
     equal to that term instead, the different merge seen before.
   - Z3's `context::is_shared` (`smt_context.cpp:4830-4903`) keeps its answer in the root's
     `m_is_shared` (`smt_enode.h:80, 196-208`). It clears it only when an enode is created over
     the class (`smt_enode.cpp:52, 57`) and on a merge or its undoing (`smt_context.cpp:588,
     994`), not when a pop deletes a parent. Here Z3 answers from a stale `true`, where a fresh
     computation says false. `isShared` (`theory-lra-model.ts:208-218`; `theory_lra_model.rs:286`
     on `smt-decide`) computes afresh each time.
   - With the cache in the enode (`enode.ts:51`; `enode.rs:337`) and cleared in `mkEnode`,
     `addEq` and `undoAddEq` (`internalizer.ts:604`, `context.ts:510, 594`; `internalizer.rs:616`,
     `context.rs:1037, 1135` on `smt-decide`), the TypeScript proves the input with Z3's whole
     stream of 19,846 instances. With the third and fourth fixes, `cb7b13d3236da8ea`,
     `ee2307985b84e424`, `52c873767bacfb3b`, `024f5dc53f8b63a5`, `fa51a87ba4ebf399` and
     `8df9b72d29f8a626` keep Z3's streams.

**Status: causes 1 to 4 were fixed in Rust toward Z3 5.3.3** (ab973e2, dbbcb78, 42f742f, b385778);
causes 1 and 4 now follow Z3 4.8.9 instead, as above. The TypeScript
is deleted; the SMT tables' lines the fixes move were printed by its scripts with the same fixes
(`smt/tests/tables/README.md`). The record is recalibrated on the Rust decider (a692935, P0 above).
Of the 13 inputs above, 12 follow Z3:

- `cb7b13d3236da8ea`, `ee2307985b84e424`, `52c873767bacfb3b`, `024f5dc53f8b63a5`,
  `d542f926ff5ed013`, `fa51a87ba4ebf399`, `beb7dd1741444a77` and `41a69bf765dd7c8b` are `unsat`
  with Z3's number of instances (471, 1,257, 2,343, 1,045, 53,000, 8,000, 604,603 and 19,846).
- `8df9b72d29f8a626`, `1319a2956705afce`, `fe8845daad4c648e` and `5e53b781a834c8ec` stop at their
  step limits, as Z3 times out, and the Rust's whole stream there is Z3's: 118,840, 436,546, 28,303
  and 86,967 instances, against Z3's streams on the text with the names written in, which on these
  four are Z3's own.
- `0c812b0a8aa1347b` stops at its step limit, as Z3 times out, but its stream is Z3's for 365,521
  instances only: the 365,522nd is Z3's `k!52` and the Rust's `k!42`. Not traced yet. The
  hypothesis is the hold on a builtin declaration above, which the Rust still counts as the
  TypeScript did (the NaN); the candidate fix is smt-core.md §4's: release the aux context's last
  counterexample model before the model checker pops its scope, which gave Z3's stream on every
  input that told the two apart, once the line in Z3 that releases it is found.

The step-limit cases need no decider fix: at the recalibrated limits the Rust proves the 24 that the
fixes had left at the TypeScript's limits, and `5c4b35bdc13bbc89`, each with Z3's number of
instances. Two remain: `5390a15510ed57e1` and `c4f10dabeaca0a49` prove with Z3's 70,639 and 442,772
instances given 2,570,874 and 10,358,109 steps, above their limits of 1,763,840 and 10,021,636. One
input is new: `f0570424f250a4cc`, `unknown` at the TypeScript's limit, the Rust proves at its new
one with 30,027 instances, leaving Z3 at the 12,937th (Z3's `k!43`, the Rust's `k!106`). Z3 times
out at 5 s and 50 s, but proves the text with `smt.random_seed=1`, so the `unsat` holds.
