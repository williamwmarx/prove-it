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
`deciders.ts` maps a prover name to `(text, {timeLimitMs, signal}) => Verdict`, and the worker
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
   the decider corpus with its step limit, by the Rust port through the addon (`--side rust`) or by
   the TypeScript (`--side ts`), and compares verdict and statistics with the record;
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
 prove.ts (TS)            decide(prover, text, limits) ──► DECIDERS[prover]
                                                           ├─ TS decider     (default until its flip)
                                                           └─ native decide  (addon / wasm)
```

- One binding call, as built in P0 (`prove-it-host/src/prover.rs`, ABI 12): `decide(prover,
  text, timeLimitMs, stepLimit | undefined, cancel | undefined)` returns `{kind: "decided",
  verdict, statistics}`, `{kind: "error", message}` (thrown as a `TlaProverError`) or `{kind:
  "declined", reason}`. It runs on a thread with a 256 MB stack. Strings cross once per decision; a
  decision takes milliseconds to seconds, so the 15–160 ns crossing (DESIGN 10.1) is noise.
  WebAssembly exports it as `prove_it_decide` through the `call()` ABI and reads the clock from the
  `prove_it_now` import the engine already uses.
- `src/prover/deciders.ts` chooses per prover: `PROVE_IT_PROVER=ts|rust` forces all, and
  `PROVE_IT_PROVER_<NAME>=ts|rust` one back end, such as `PROVE_IT_PROVER_ZENON` (for the
  differential and for bisecting). The default for each back end flips to `rust` in the PR that
  makes its differential clean, by adding it to `RUST_BACKENDS` in `deciders.ts`. If no addon
  loads, or the Rust port declines the input, the TypeScript decider runs (`PROVE_IT_ENGINE=debug`
  reports it), until P7 deletes it; then `prove` follows `check`'s
  rule (fallback.md): the WebAssembly module, or `EngineUnavailableError`.
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
  across threads, so `Rc`, not `Arc`. Blast's prototerms with mutable variables become arena
  indices into a per-search variable table (undo trail as now).
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
| `prove-smt` | Z3 (`src/smt`, `src/ast`, `src/math/lp`, `src/nlsat`, `src/util`) | MIT | the Z3 section names `native/crates/prove-smt/`; `z3-license.txt` moves with the code |
| `prove-num` | Z3's `rational`/`mpz` semantics, written fresh on JS `bigint`'s rules | MIT (Z3's where it follows `rational.ts`) | under the Z3 section |
| `prove-zenon` | Zenon as tlapm ships it, with its TLA+ extension | BSD-3-Clause-style (INRIA) | the Zenon section names the crate; the crate keeps the `LICENSE` beside the code, as `src/prover/zenon/LICENSE` |
| `prove-zenon` (`ocaml` module) | OCaml's `Hashtbl.hash` (`runtime/hash.c`), `List.sort`/`List.stable_sort` | LGPL-2.1-only with OCaml's linking exception | the OCaml section lists the Rust file |
| `prove-isabelle` | Isabelle2025's Pure, Isar, Provers (BSD-style, Cambridge/TUM), and Isabelle/TLA+'s theories and ML setup as tlapm ships them (BSD, tlapm's licence) | BSD-3-Clause-style | the Isabelle section, and the tlapm section for the logic data and `tla/`; `LICENSE` and `LICENSE-tlapm` move with the code |
| `prove-ptl` | tlapm's PTL backend input; the decider is our own | MIT, tlapm's BSD for what `ptl/encode.ts` ports | tlapm section |
| `prove-obligations` | tlapm (obligations, Prep, encoders, `.tlacache`, TLAPS.tla verbatim) | BSD-2-Clause-style (INRIA, Microsoft, Linux Foundation) | tlapm section |
| `prove-obligations` (`format`, `marshal`, the `getHash` of `action`) | OCaml's `Format` (`stdlib/format.ml`), Marshal (`runtime/intern.c`, `extern.c`), `runtime/hash.c` | LGPL-2.1-only with OCaml's linking exception | the OCaml section lists the Rust files |

The package's `"license": "MIT AND LGPL-2.1-only WITH OCaml-LGPL-linking-exception"` comes from
the four OCaml ports alone (`tlapm/ocaml-marshal.ts`, `zenon/ocaml.ts`, `obligations/format.ts`,
`action.ts`'s `getHash`). Their Rust ports inherit it: they are translations of the same code. So
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
bun scripts/run.ts prover-inputs                     # writes .prover-inputs/ from the record, minutes
bun scripts/run.ts prover-differential --side rust --prover zenon --jobs 4
```

`--side ts` checks the record against the TypeScript (it reproduces), `--filter` keeps inputs by
digest, and `.prover-differential.json` holds every result. Outcomes: `same`, `differs`,
`unstable` (2.3), `declined` (not covered by the port yet), `crash`. With
`PROVE_IT_ENGINE_WASM=dist/prove-it-engine.wasm` the Rust side is the WebAssembly module. A track
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
a sample (`--filter tlapm/library`); the size row is recorded (3.9); and the full local gate of
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

- Phase 1: this document.
- P2 Zenon: `prove-zenon` ports all of `zenon/` but `encode.ts`, one module per TS file, behind
  `PROVE_IT_PROVER`. `tests/zenon.rs` ports `zenon.test.ts` on its fixtures (the checker's tests
  are in `src/check.rs`); `scripts/zenon-fixtures.ts` records what the TypeScript decides on each
  fixture under a step limit into `tests/fixtures/zenon/decisions.txt`, which the Rust matches in
  verdict, steps, every statistic and the proof's digest. Malformed input is declined. Next: the
  decider differential on the corpus's `.znn` inputs, then the flip commit.
- P3b-lp (`prove-smt` module `lp`): every file of `smt/solver/lp/` is ported except `nra-solver.ts`,
  which is ported on top of the nlsat port and lands after it. Until then `NraSolver::check` and
  `check_assignment` decline with `SmtError::Unsupported`, so a check that reaches nlsat is
  declined, never answered. The architecture, written at the top of `lar_solver.rs` and
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
    `scripts/lp-trace.ts`) against the Rust lp. On the 45 `tests/fixtures/smt` inputs and 7
    nonlinear ones it gives 47 same and 0 differs. The other 5 are declined at `NlaCore`,
    whose replay is next.
  - **Next:** run the trace on every SMT input of the decider corpus once its record is on
    `main`. Then nra-solver, after nlsat. Then P3c's theory-lra glue, which calls lp exactly as
    the trace does.
