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

**Handles.** Expressions, sorts, declarations, Boolean variables, literals, clauses, theory
variables: `u32` where the TS never stores -1 in them, `i32` where it does (a TS `Int32Array` slot
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

**The manager.** `AstManager<'l>` holds the `ResourceLimit<'l>` (lifetime of the decision's
`Limits`). A TS class that keeps `private manager: AstManager` keeps no manager in Rust: its methods
take `m: &mut AstManager<'_>` (or `&AstManager` when they only read) as their first argument after
`self`. `Context` owns its manager as the field `m`.

**The context.** `Context extends Internalizer`: one `struct Context<'l>` in `core/context.rs`,
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

- P3a: done on branch `smt-foundation`.
- P3c: conventions fixed (this note); wave 1 next.
