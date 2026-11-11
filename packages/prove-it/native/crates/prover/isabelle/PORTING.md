# Porting `src/prover/isabelle` to `prove-isabelle`

The port is done and the TypeScript it ports is deleted; this file stays as the record of how its
idioms became Rust.

The working rules for the port of the Isabelle back end (design/prover.md, P4a and P4b). Read
`AGENTS.md` at the repository root, and `packages/prove-it/native/design/prover.md` §3.3, §3.6
and §4a, first. This file says how the TypeScript's idioms become Rust in this crate, so that
modules ported separately fit together.

## Layout

- One Rust module per TypeScript file, in the same directory, in snake case:
  `src/prover/isabelle/pure/term-ord.ts` is `src/pure/term_ord.rs`, `provers/blast/prove.ts` is
  `src/provers/blast/prove.rs`. Register it in the directory's `mod.rs`.
- Keep the TypeScript file's header comment (what it ports, from where, its licence) as the
  module's `//!` comment, and keep its explanatory comments, as `///` on the item they describe.
- Keep the TypeScript's names in snake case (`fastypeOf1` is `fastype_of1`, `HAS_VAR` stays).
  Types keep their names in camel case (`TyEnv`, `MatchEnv`).
- Port literally: the same functions, the same order of operations, the same traversal order. The
  goal is the same search step for step (the decider differential compares the number of
  interrupt checks), not the same answer by another route.

## The foundation (`error.rs`, `pure/{term,seq,interrupt,list}.rs`; read them first)

- **Terms and types** are `Term` and `Typ`, `Rc` handles to `TermNode`/`TypNode`; match on
  `&**term`. Names are `Name` (`Rc<str>`), sorts `Sort` (`Rc<[Name]>`, always `empty_sort()` in
  Isabelle/TLA+). `Var` is a `Term` known to be a Var. Indexes (Var index, Bound index, maxidx,
  loose) are `i32`.
- **Equality.** `Term` and `Typ` implement no `PartialEq`. The TypeScript's `left === right` on
  terms or types is `Term::ptr_eq`/`Typ::ptr_eq`; `aconv`, `eq_term` and `eq_typ` are what they
  say. Rebuilders return the same `Rc` when nothing changed (`update_app`, `update_abs`), as the
  TypeScript returns the same object; keep that wherever the TypeScript does it, since later
  `===` checks depend on it.
- **Exceptions.** Every function that can throw, directly or through what it calls (including
  pulling a sequence and `check_interrupt`), returns `Res<T>` (`error.rs`) and propagates with
  `?`. `new TlaIsabelleError("THM", message)` is `Err(thm_exn(message))` (also `term_exn`,
  `type_exn`, `error_exn`). The local exception classes (pattern's Unif/NotPattern/Match, unify's
  CantUnify/ChangeFail, thm's Compose, rewriter's MatchFailure, hypsubst's NoMatch/EqVar, blast's
  Trans and Backtrack) are variants of `Error`. A `catch` that handles some errors and rethrows the
  rest is a `match` on the `Err` that returns the rest. Never panic for an exception; `unreachable!`
  only where the TypeScript's types make the case impossible.
- **Interrupts.** The TypeScript threads a `limits: Limits` through contexts and closures and calls
  `checkInterrupt(limits)`. Here the decision's limits are installed for the thread
  (`interrupt::with_limits`), so `checkInterrupt(limits)` is `check_interrupt()?` with no argument,
  and the `limits` parameters and fields disappear. Call it at exactly the TypeScript's places: each
  call is a counted step. Where the TypeScript passes `limits` as `undefined` (the unifier then
  checks nothing), wrap the call in `without_limits(|| …)` and force every sequence inside it.
- **Stack.** The TypeScript relies on JavaScript's stack overflow ending a hopeless proof
  (decide answers unknown). Rust can't catch an overflow, so each recursive function that returns
  `Res` and can recurse as deep as a term or a proof search (the rewriter, the unifier, pattern
  unification, the simplifier, blast's search) enters a level with `let _depth = check_stack()?;` on entry and keeps the guard until it returns
  (a depth count: 20,000 natively, 1,000 in WebAssembly; the guard is `#[must_use]`).
- **Lazy sequences** are `Seq<T>` (`pure/seq.rs`): `make_seq`, `defer_seq` (whose closure may hand
  over to another sequence, `Step::Seq`, where the TypeScript's `deferSeq` returns a `Seq`),
  `pull()` returning `Res<Cell<T>>`, and the combinators with fallible callbacks. A TypeScript
  `Tactic = (state: Thm) => Seq<Thm>` may throw when applied, so it is `Rc<dyn Fn(Thm) ->
  Res<Seq<Thm>>>` (`tactical.rs` defines `Tactic` and `GoalTactic`).
- **ML lists** with shared tails are `List<T>` (`pure/list.rs`).

## Collections and numbers

- A `Map` or `Set` that is ever iterated, spread, or turned into an array becomes a `Vec` (of
  pairs) or an insertion-ordered map; deletions keep the order of the rest (`Vec::remove`, never
  `swap_remove`). A `Map` used only with `get`/`has`/`set` may be a `HashMap`. Iterating a std hash
  map or set is refused by `crates/prover/clippy.toml`.
- A `WeakMap` or `Map` keyed by object identity is keyed by `Term::address()`, and must hold a clone
  of the key term (in the value) so that the address is not reused while the entry exists.
- `array.sort(cmp)` is `sort_by` (stable) with the comparator ported literally.
- JavaScript numbers used as counts or positions are `usize`; as indexes of terms, `i32`;
  `| 0`/`>>> 0`/`Math.imul` are wrapping `i32`/`u32` operations.
- Strings: names are ASCII (decide declines other input), so byte order and byte length are
  JavaScript's code-unit order and length.

## Data structures shared across modules

- Objects that the TypeScript shares and never mutates are `Rc<Struct>` or plain `Clone` structs.
  Objects it mutates in place (`Map` updated in place, arrays pushed to while shared) are
  `Rc<RefCell<…>>`; never hold a `RefCell` borrow across a call that may re-enter.
- Optional fields are `Option`; TypeScript unions of object kinds are `enum`s.

## Test expectations

The tests compare with what the TypeScript gave, recorded in `testdata/`. The TypeScript is
deleted, and the script that recorded them with it, so nothing rewrites them now: a change to a
line is a change to the port's search.

## Checks

Before handing back: `cargo fmt -p prove-isabelle`, then in `packages/prove-it/native`
`cargo clippy -p prove-isabelle --all-targets -- -D warnings` and `cargo test -p prove-isabelle`
must pass with your modules registered. Standard library only; no `unsafe`. Don't edit modules other agents own, except to register yours in a
`mod.rs`; if you need something from a module that is missing or has the wrong shape, say so in
your report rather than working around it silently.
