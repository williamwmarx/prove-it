# Porting the SMT core to Rust

Stage P3a and P3c of `design/prover.md` (§4b): `src/prover/smt/solver/*.ts` to the crate
`prove-smt` (`native/crates/prover/smt`). This note fixes the conventions that every module of the
port follows, so that modules ported in parallel fit together. It is the resumable record of the
track: keep it current.

## 1. What exists

| Module | Ports | State |
|---|---|---|
| `prove_num::{Int, Rational}` | JS `bigint`, `rational.ts` | done; tables against JS in `num/tests/tables` |
| `util::hash` | `hash.ts` | done; tables against TS |
| `util::hashtable::{ObjMap, ObjHashtable}` | `hashtable.ts` | done; slot order against TS |
| `util::lbool::LBool` | `lbool.ts` | done |
| `util::random_gen::RandomGen` | `random-gen.ts` | done; table against TS |
| `util::rlimit::ResourceLimit` | `rlimit.ts` (not V8's heap check) | done |
| `util::error::SmtError` | the `Smt*Error` classes of `src/errors.ts` | done |
| `util::ordered_map::{OrderedMap, OrderedSet}` | an iterated JS `Map`/`Set` | done |
| `lp::dependency` | `lp/dependency.ts` | done |
| `core::{ast, flat_literals, ref_vector, expr_ref}` | the AST manager | done; a 3000-step trace of the TS manager (ids, hashes, small ids, ref counts, recycling) in `smt/tests/tables/ast.txt`, written by `scripts/smt-core-tables.ts` |
| `core::{literal, sort, enode, cg_table, case_split_queue, sticky_generations, clause}` | the e-graph's and the clauses' types | done; `smt-clause-store` ported |
| `core::{smtlib_parser, goal}` | the SMT-LIB reader, goals | done; all 46 `tests/fixtures/smt` and 52 of 54 short scripts against the TS (`smt/tests/tables/parser.txt`, `scripts/smt-parser-tables.ts`); the two skipped are listed in `tests/parser.rs` |
| `core::{act_cache, rewriter_tpl, var_subst, expr_safe_replace, ast_lt, ast_util}` | the rewriter template and substitution | done; a 6,192-line TS trace (results, ids, step counts, ref counts) in `smt/tests/tables/rewriter.txt`, written by `scripts/smt-rewriter-tables.ts`. A rewriter's configuration is a `RewriterConfig` trait (module header of `rewriter_tpl.rs`) |
| `core::{context, internalizer, relevancy, conflict_resolution, dyn_ack}` | the CDCL kernel with the E-graph | done; `context.rs`'s unit tests (propositional, EUF, pigeonhole, 3-SAT, dynamic Ackermann) expect the TS numbers `scripts/smt-kernel-reference.ts` prints |
| `core::{nnf, pull_quant, pattern_inference, maximize_ac_sharing, qe_lite_fm}` | NNF and skolemization, quantifier pulling, pattern inference, AC sharing, Fourier–Motzkin | done; about 10k lines of TS trace over random terms and every fixture's assertions (`smt/tests/tables/nnf.txt`, `scripts/smt-nnf-tables.ts`). `MAX_SPLITS` bounds only the work of pattern inference's search, never its result, so no table can pin it |
| `core::{fingerprints, mam_compiler, mam_interpreter, e_matching, qi_queue, quantifier_manager}` | E-matching and quantifier instantiation | done; seven quantified problems give the TS's result, conflicts, steps and instances, and the compiled code trees equal the TS's dump (`scripts/smt-ematching-reference.ts`), all with the arithmetic theory set up |
| `core::{poly_rewriter, arith_rewriter, der, rewriter}` | th_rewriter | done; 25 seeded episodes and every fixture's assertions under five option sets, with a cancellation at the same step (`smt/tests/tables/th-rewriter.txt`, `scripts/smt-th-rewriter-tables.ts`). With it the E-matching problems match the TS step for step. The TS rewriter does not terminate on some random terms (`(= (is_int (* … s s …)) p)` with `isPullingCheapIte`), so the table runs each episode under a step budget |
| `core::{asserted_formulas, propagate_values, ctx_simplify, qe_lite_der, qe_lite, quant_tactics}` | the preprocessing before the search | done; every fixture and 300 seeded random quantified scripts through the pipeline `solver.ts` runs, each stage alone, and asserted formulas with push/pop, with budgeted cancellations (`smt/tests/tables/tactics.txt`, `scripts/smt-tactics-tables.ts`) |
| `core::{proto_model, model_evaluator, model_generator}` | models: interpretations, evaluation, completion, the model of a search | done; hand-built models and ground EUF/propositional searches against the TS (`smt/tests/tables/models.txt`, `scripts/smt-model-reference.ts`) |
| `core::{auf_solver, model_macro_solver, quantifier_analyzer, model_finder, model_checker}` | model-based quantifier instantiation | done; thirteen quantified EUF problems without patterns, which only MBQI decides (sat by macros, quasi-macros and projections, unsat by model-based instances over several rounds), give the TS's result, conflicts, steps, instances, ASTs and model (`smt/tests/tables/mbqi.txt`, `scripts/smt-mbqi-reference.ts`). The model checker's auxiliary context shares the main context's manager by swapping it in for each of its operations (`model_checker.rs`'s header) |
| `core::theory_lra*` | `theory-lra*.ts`, the arithmetic theory | done; one module per TS file, the state a struct `TheoryLra` held as `Context::theory` and its methods `impl Context` methods (`lra_*`, the kernel's `theory_*`), as the header of `theory_lra_state.rs` describes, with how it owns and calls `LarSolver`, `BoundPropagator`, `IntSolver` and `NlaCore`. 116 arithmetic problems (Int and Real, bounds, (dis)equalities, ite, div and mod, nonlinear products, theory combination, models; 80 of them seeded random) and solver.ts's `checkSmt` on all 45 `tests/fixtures/smt` scripts give the TS's result, conflicts, steps, instances, ASTs and models (`smt/tests/tables/lra.txt`, `scripts/smt-lra-reference.ts`). nlsat's model is read through `lp::nra_solver` (`NraSolver::value`, its algebraic manager) as the TS reads it: `mk_value`, `is_eq` and `assume_eqs` under `is_using_nra_model`, which the nine `nra-*` problems pin (shared variables, terms and integers compared in nlsat's model, rational model values, and the TS's `SmtUnsupportedError` on an irrational one) |
| `core::solver`, `prove_smt::decide` | `solver.ts` (`checkSmt`, `decideSmt`) and `decideZ3` | done; declines nothing but a port bug: as `decideSmt`, a cancel or the step limit is unknown with its `stop`, `SmtError::Unsupported` unknown with `stop=unsupported`, a parse error `DecideError::Prover`; every other error (`SmtError::Invariant` above all) is `DecideError::Declined`, never a verdict. `tests/unit/smt.test.ts` case for case in `smt/tests/smt.rs`, all with the TS's expectations, and all 45 fixtures' verdicts and statistics (`instances`, `steps`, `stop`) identical to `decideSmt`'s (`smt/tests/tables/decide.txt`, `scripts/smt-decide-reference.ts`) |
| `core::*` | the rest of `smt/solver/*.ts` | §3 |

The tables are written by `scripts/smt-foundation-tables.ts` (`bun scripts/smt-foundation-tables.ts`)
from the TypeScript, and replayed by `cargo test -p prove-num -p prove-smt`.

## 2. Conventions

**Layout.** One Rust module per TS file, `core/<snake_case>.rs` (`rewriter-tpl.ts` →
`core/rewriter_tpl.rs`), listed in `core/mod.rs`. Keep each file's port header (what it ports, from
where, MIT) and its explanatory comments. TS names in snake case (`mkApp` → `mk_app`), types keep
their names. Constants keep their names in upper snake case.

**Reference counting is ported, not dropped.** `ast.ts` ports Z3's reference counts, its id
recycling (`ids`, `freeIds`, the free list of small ids) and `withTemporaries`, because Z3's ids
order its sorts and the matcher hashes small ids. So `inc_ref`, `dec_ref`, `release_later`,
`begin_temporaries`/`end_temporaries` and `RefVector` are ported literally, every call kept at the
same place. (This corrects §3.3 of prover.md, which assumed the arena made them unnecessary.)

**Handles.** `ast::{Expr, Decl, Sort}` are `i32` (the TS stores -1 in each); `literal::{BoolVar,
Literal}`, `clause::Clause`, `enode::{EnodeId, JustificationId}` are `u32`. Other handles (theory
variables and the like): `u32` where the TS never stores -1 in them, `i32` where it does (a TS `Int32Array` slot
that holds -1 stays an `i32`). Type aliases from the module that owns them (`ast::Expr`,
`literal::Literal`, `literal::BoolVar`, `clause::Clause`), no newtypes, so the arithmetic on them
(`literal ^ 1`, `literal >> 1`) ports as it reads. A TS `Uint32Array` is `Vec<u32>`, an
`Int32Array` `Vec<i32>`, a `Uint8Array` `Vec<u8>`; the TS's doubling (`grow`) is a `Vec`'s own, so
"a caller does not keep one across the creation of an expression" no longer matters.

**Objects with identity become arenas.** A class whose instances are compared with `===`, used as
`Map`/`Set` keys, or linked to each other (`Enode`, `Justification` and its subclasses, the MAM's
code trees, `FuncInterp`, the model finder's `Node`) becomes a `Vec` owned by the component that
creates them, indexed by a `u32` handle (`enode::EnodeId`). Slots are never reused within a check,
so a handle never aliases a newer object. A class hierarchy with an abstract method
(`Justification.getAntecedents`) becomes one `enum` with a `match`.

**The manager.** `AstManager` holds the `ResourceLimit`, which holds a clone of the decision's
`Limits` (no lifetime: `Limits` is a shared `Rc`; nothing keeps either after `decide` returns). A TS
class that keeps `private manager: AstManager` keeps no manager in Rust: its methods
take `m: &mut AstManager` (or `&AstManager` when they only read) as their first argument after
`self`. `Context` owns its manager as the field `m`.

**What `ast` settled** (follow it in callers): `mk_app(decl, args: &[Expr], sort)` takes a slice
(the TS `start` argument is `&stack[start..]`); the `mk_*` that can throw return `Result`;
`with_temporaries(body)` keeps the result and `with_temporaries_keeping(body, get_kept)` takes the
TS's `getKept`; `map_args`/`some_arg`/`every_arg` only read, so a caller that builds per argument
loops over `get_arg`; `FlatLiterals.add` is the manager's `flat_literals_add`. `RefVector` and
`ExprRef` take `&mut AstManager` and release nothing on drop: the owner calls `reset` where the TS
object would be released (end of scope of a Z3 `expr_ref_vector`).

**The context.** `Context extends Internalizer`: one `struct Context` in `core/context.rs`,
with the fields of both classes. `internalizer.rs` holds `impl Context` with the internalizer's
methods. A class that keeps `private context: Context` (`ConflictResolution`, `DynAckManager`,
`Mam`, `Compiler`, `Interpreter`, `QiQueue`, `DefaultQuantifierManager`, `ModelChecker`,
`ModelFinder`, `QuantifierAnalyzer`, the `theory-lra-*` state) becomes a struct of its own fields,
held by `Context` as a field named after the TS property (`conflict_resolution`, `qmanager`,
`theory`), and its methods that reach the context are `impl Context` methods in that class's
module, named `<class prefix>_<method>` when the name would clash (`mam_add_pattern`). Reading
`this.context.x` is `self.x`; reading the class's own `this.y` is `self.<field>.y`. A method that
touches only its own fields stays on its struct.

**Interfaces passed instead of the context** (`CaseSplitContext`, `RelevancyContext`,
`Antecedents`, `OnMatch`) become traits, implemented by `Context` or by a small adapter struct.

**Closures.** A TS closure that is stored (`trailClosures`, the clause store's `delEhs`, the MAM's
`onMatch`) becomes an `enum` of the closures the TS actually creates, with the captured values as
fields, applied by a `match` where the TS calls it. A closure only passed down and called at once
stays a Rust closure (`impl FnMut`).

**Errors.** Where the TS throws, the Rust returns `Result<_, SmtError>` and propagates with `?`:
`SmtCanceledError` → `SmtError::Canceled` (from `checkpoint()?`), `SmtInvariantError` →
`SmtError::Invariant`, `SmtUnsupportedError` → `Unsupported`, `SmtParseError` → `Parse`. A
function that cannot throw returns its value. Never `panic!`, `unwrap()` or `expect()` on a path the
input can reach; `unreachable!` only for a state the code itself rules out.

**Maps and sets.** A `Map`/`Set` that is iterated, spread or turned into an array is an
`OrderedMap`/`OrderedSet`; one only used with `get`/`has`/`set`/`delete` may be a `HashMap`/
`HashSet` (the crate's `clippy.toml` refuses iterating those). A `Map` keyed by a string built only
to be a key (`${a},${b}`) may be keyed by a tuple instead, when it is never iterated. `ObjMap` stays
`ObjMap` (its slot order is Z3's).

**Numbers.** `bigint` is `prove_num::Int`; `Rational` is `prove_num::Rational`. `| 0`, `>>> 0` and
`Math.imul` are `i32`/`u32` wrapping arithmetic. A float stays `f64` with the same operations in the
same order. `array.sort(cmp)` is `sort_by` (stable, as JS), the comparator ported literally;
`sortByKey`/`sortNumbers` (`sort.ts`) are stable sorts by key and port as `sort_by_key`.

**Where the port refuses what the TS accepts.** `SmtError::Invariant` from the Rust where the TS
goes on (so far: a nullary `(and)`, `(or)`, `(=)`, whose TS declaration hash reads `undefined`
sorts, matching neither Z3 nor any input tlapm writes) must reach `decide` as
`DecideError::Declined`, so the TypeScript decides it; never as a verdict.

**Recursion.** Where the TS recurses on terms and relies on catching a stack overflow
(`isStackOverflow` → unknown), the Rust counts depth and returns `SmtError::Unsupported` past a
fixed depth, before the native stack would overflow on the decision's 256 MB thread.

**Statistics and steps.** Every `limit.inc()`/`checkpoint()` of the TS is kept at the same place:
the step count is the first thing the differential compares.

**Tests.** Each module ports the TS unit tests of its code to `#[test]`s, case for case. The core's
first gates are `tests/unit/smt-clause-store.test.ts` (in `core/clause.rs`) and
`tests/unit/smt.test.ts` (in `crates/prover/smt/tests/smt.rs`, on `tests/fixtures/smt`).

## 3. Order and fan-out

Dependency order (imports within `smt/solver`), each wave ported in parallel, one subagent per
group, integrated and tested before the next:

1. `literal`, `sort`, `enode`, `cg-table`, `case-split-queue`, `sticky-generations`, `clause`
   (gate: `smt-clause-store`); and in parallel `ast`, `flat-literals`, `ref-vector`, `expr-ref`.
2. Rewriters: `act-cache`, `rewriter-tpl`, `var-subst`, `expr-safe-replace`, `ast-lt`,
   `ast-util`, `poly-rewriter`, `arith-rewriter`, `der`, `rewriter`. In parallel the parser
   (`smtlib-parser`) and `goal`.
3. Simplification: `nnf`, `pull-quant`, `pattern-inference`, `maximize-ac-sharing`,
   `asserted-formulas`; tactics: `propagate-values`, `ctx-simplify`, `qe-lite-der`, `qe-lite-fm`,
   `qe-lite`, `quant-tactics`.
4. The kernel: `relevancy`, `internalizer`, `context`, `conflict-resolution`, `dyn-ack`; quantifiers:
   `fingerprints`, `mam-compiler`, `mam-interpreter`, `e-matching`, `qi-queue`,
   `quantifier-manager`; models: `proto-model`, `model-evaluator`, `model-generator`, `auf-solver`,
   `model-macro-solver`, `quantifier-analyzer`, `model-finder`, `model-checker`; then `solver`
   (gate: `smt.test.ts` on inputs without arithmetic atoms, with `decide` declining the rest).
5. `theory-lra-*`, once `lp` lands (P3b-lp).

## 4. Handoff

- P3a (#229), P3c part 1 (#242) and part 2 (#252) are on main. Part 3 is the arithmetic theory, `solver` and `decide`: every fixture and every case of `smt.test.ts` as the TS does, statistics included, and the decider corpus (`prover-differential --side rust --prover smt`, prover.md §4a) the same on all 10,320 smt and 56 z3 inputs. The flip to Rust is its own commit.

### TypeScript deviations from Z3

Where the TS does what Z3 does not, the port mirrors the TS until the flip, so that the differential stays exact; each is then fixed on both sides, with the inputs it moves re-recorded.

- A model's hold on a builtin declaration (`div0`, `mod0`): `ast.ts`'s `incDeclRef` and `decDeclRef` count it in `declRefCounts`, which has no entry for it, so the count is NaN and each time a model drops the declaration it is released and its small id freed, while its applications, counted under its signature, still hold it. Z3 counts an application's and a model's references on the one `func_decl`, and keeps it. It moves `getNumAsts`, which seeds MBQI's model completion, and so the search and, under the step limit, verdicts. The Rust mirrors it with `decl_ref_counts: Vec<Option<i32>>` (`None` is the NaN); regression input `smt/tests/inputs/builtin-decl-release.smt`. The evidence (TS, Rust and Z3 lines), the verdict it changes and the five inputs it moves are in prover.md's Handoff, "TypeScript deviations from Z3". To fix on both sides: count a model's hold under the declaration's signature, with its applications.
