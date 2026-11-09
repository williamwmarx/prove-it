# The trace evaluator (`tla-trace`)

TLC prints the states of a trace as it rebuilds them, so the text of a value can depend on how
TLC built it. The engine's store interns values and keeps none of that (DESIGN.md §2.8). Today
the TypeScript interpreter rebuilds the path (`check.ts` `resumeFromEngine`, `getPathStates`,
`findStepAction`, `toTrace`). This is the Rust replacement: a printing-only evaluator in a new
crate, `tla-trace` (std only), that re-evaluates the path from the engine IR on a value tree of
its own and returns each state's values as TLC prints them. It also re-evaluates where the engine
failed, so it can give TLC's run-time error messages with their values. This file is the plan,
followed by notes as built.

## What TLC does

Read in tlaplus/tlaplus (`tlc2.tool`, `tlc2.value.impl`):

- **The search fingerprints a state before it checks it.** `ModelChecker.DoInitFunctor` does
  `if (inModel) { fp = curState.fingerPrint(); ... }`, then checks the invariants. `doNext` sets
  `inModel = isInModel(succ) && isInActions(cur, succ)`, fingerprints in `isSeenState` only when
  `inModel` holds, and then checks the invariants of an unseen successor. So TLC fingerprints a
  state that violates an invariant unless the state fails a CONSTRAINT or an ACTION_CONSTRAINT.
- **Fingerprinting normalizes.** `TLCStateMut.fingerPrint` fingerprints each value. Without a
  VIEW or SYMMETRY, `RecordValue.fingerPrint` calls `normalize()`, which sorts the fields in
  place. So do `FcnRcdValue` and `SetEnumValue`. A VIEW calls `deepNormalize` on each value.
  `FcnLambdaValue.fingerPrint` builds and caches its `FcnRcdValue` (`fcnRcd`), which prints from
  then on.
- **A sorted record is in intern order.** `RecordValue.sort` and `StringValue.compareTo` compare
  `UniqueString`s, and `UniqueString.compareTo` is `this.tok - other.tok`: the order in which TLC
  first interned each text. That is the IR's ranked string order (`createTlcOrder`), which the
  store keeps. Walgit's initial state shows it: `manifest = [logSegments |-> {}, headSeq |-> 0,
  checkpoint |-> None, version |-> 1]` is the order of the ranks (388, 433, 451, 477), not the
  alphabetical one.
- **A trace is rebuilt from fingerprints.** `TLCTrace.getTrace` walks the path of fingerprints.
  `Tool.getState(fp)` enumerates the initial states, and `Tool.getState(fp, s)` the successors of
  `s` action by action, and each returns the first state whose fingerprint matches. So each
  rebuilt state is fingerprinted, and therefore normalized, before it prints. Each step's label
  comes from `TLCStateInfo`: the action that generated it.

So in a trace of fingerprinted states, a record prints in the store's order. What still depends
on construction is the following:

- **`IntervalValue`.** It stays an interval when fingerprinted and prints `1..3`. The store can't
  tell it from `{1, 2, 3}`, so `is_printable` refuses every set of consecutive integers,
  singletons included.
- **Lazy sets TLC keeps.** These are `SubsetValue`, `SetOfFcnsValue`, `SetOfRcdsValue`,
  `SetOfTuplesValue`, `SetCupValue` and the like, `UnionValue`, and `SetPredValue`. In a state each
  prints expanded where it can be enumerated, and as written otherwise
  (`getExpandedLazySet`, `formatLazySet` in values.ts).
- **`RecordValue` against `FcnRcdValue`.** A one-key function whose key is a string that isn't a
  field name prints as a record only if it is a `RecordValue`.

Written order matters where TLC prints a value it hasn't normalized:
- the last state of a violation outside the constraints;
- an ALIAS, whose record TLC builds per state;
- Print and PrintT output, where `formatPrinted` normalizes but a lambda's range is evaluated
  afresh;
- ToString;
- the values in a run-time error message, such as `Attempted to apply function:\n<f>\n...`.

The TypeScript interpreter models each of these rules: `writtenKeys`, the hash and fingerprint
that mark a value sorted, `forgetWrittenOrder` on comparison, `markFingerprinted`, and the
function classes. It prints what TLC prints on 1460 of the 1466 differential runs, so it is the
reference for the port. TLC is the reference where the two disagree.

## Approach

The evaluator has a value representation of its own, with the engine IR as input. It never
interns into the search's store. It only reads that store, to match states.

- **Values** (`value.rs`) mirror the TypeScript `Value`, as reference-counted trees:
  - booleans, integers, strings and model values, each string with its TLC rank (unranked texts
    compare by their units, as the store does);
  - enumerated sets, sorted;
  - intervals;
  - functions, each with its sorted domain, range, written keys (`None` once sorted), TLC class
    (none, lambda, tuple, record) and a sorted mark that hashing or fingerprinting sets;
  - the lazy sets TLC keeps, and `Nat`, `Int`, `Real`, `STRING`, `Seq(S)`.

  The order of values is the store's `compare`, rule for rule, including its errors. A
  comparison clears the written order of what it compares, as `compareFunctions` does.
- **Expressions** (`eval.rs`) follow `evaluate.ts` kind by kind over `tla_ir::NodeKind`: names
  resolved as the compiler resolves them (locals, definitions, constants and scopes, builtins
  by name), operators expanded at the call site, recursive functions and operators by value, and
  the builtins of the standard modules the engine implements. Constants come from the IR's
  transfer encoding, which carries each function's class.
- **Actions** (`action.rs`) enumerate successors in TLC's order, as `successors.ts` and
  `Tool.getNextStates` do:
  - conjunctions left to right, assigning `x' = e` and `x' \in S` to an unassigned variable;
  - disjunctions and `\E` in the order of their sets;
  - IF, CASE and LET;
  - operators expanded;
  - UNCHANGED.

  The initial predicate is enumerated the same way.
- **Matching** (`rebuild.rs`). Each candidate is compared by value with the search's state, ids
  of the store, by a read-only walk. Equal ids in the store mean equal values, so the walk needs
  no interning. The first candidate in TLC's order that matches is the state, as `Tool.getState`
  finds it. Then it is fingerprinted, which sorts it deeply and turns lambdas into plain
  functions, as `settleRecoveredState` does. The last state of a violation is settled only if the
  search fingerprinted it: it must satisfy the constraints and action constraints, which the
  evaluator checks on its own values.
- **Printing** (`print.rs`) is `formatValue` and `formatState` over the tree. The caller pretty
  prints the result, as it does for the store's values.

The compiler's structure is reused where it fits, in how names resolve and which builtin an id
names. The compiled closures are not reused: they compute ids in a store, which is the
information this crate exists to keep.

## The API

```rust
pub struct Rebuilder<'ir> { /* the IR, the evaluator and its caches, how TLC matches a state */ }

impl<'ir> Rebuilder<'ir> {
    pub fn new(ir: &'ir Ir) -> Result<Rebuilder<'ir>, Unsupported>;

    /// TLC's trace recovery. `states` are the path's states as ids of `store`, in `ir.variables`
    /// order; `actions[i]` is the position in `ir.model.actions` of the step from `states[i]` to
    /// `states[i + 1]` (label_path), `None` to try each action as `Tool.getState` does. A step to
    /// the same state stutters. `ending` says what the last state is to TLC.
    pub fn rebuild(
        &mut self,
        store: &Store,
        states: &[&[Id]],
        actions: &[Option<u32>],
        ending: Ending,
    ) -> Result<Trace, Unsupported>;

    /// Evaluates again where the search failed, at `site`, after the path `states` (none for the
    /// initial predicate), and returns TLC's report of the error.
    pub fn evaluate_failure(
        &mut self,
        store: &Store,
        states: &[&[Id]],
        actions: &[Option<u32>],
        site: Site,
    ) -> Result<Failure, Unsupported>;
}

/// What the last state is to TLC (`known` in `toTrace`): a state the search kept (a deadlock's),
/// a violating state TLC holds as it found it (matched by value, whatever the VIEW or SYMMETRY,
/// with the state before it not rebuilt), or a lasso's (all rebuilt, no second rebuild).
pub enum Ending { Kept, Violation, Lasso }

pub struct Trace {
    pub states: Vec<TraceState>,
    /// What the spec printed as TLC rebuilt the trace again after printing it (`traceOutput`);
    /// for a trace of one state, what the initial predicate printed.
    pub trace_output: Vec<Vec<String>>,
}

pub struct TraceState {
    /// Each variable's value, in `ir.variables` order, normalized as TLC normalized it.
    pub values: Vec<Value>,
    /// What Print and PrintT printed before this state: each print as the text of each value,
    /// which the caller pretty prints and joins as it does a print during the search.
    pub printed: Vec<Vec<String>>,
}

/// Where the search failed: computing the initial states, the successors of the path's last
/// state, or the invariant at a position on the path's last state, a successor past the initial
/// states (which the caller appends, as the search doesn't keep it).
pub enum Site { Init, Next, Invariant(u32) }

/// TLC's report of the error: the code of its message, the message and its -tool text, and the
/// nested expressions it was in, which the caller prints with `format_call_stack` as message 2103.
pub struct Failure { pub code: u32, pub message: String, pub tool_message: String, pub call_stack: Vec<SourceRange> }

/// TLC's `Value.toString`; the caller pretty prints it.
pub fn format_value(value: &Value) -> String;

/// Where the evaluator can't follow TLC yet; the caller reports `not native yet: <reason>`.
pub struct Unsupported(pub String);
```

The evaluator recurses with the expressions it evaluates, so the caller runs it on a thread with a
deep stack (`tla_values::on_nesting_stack`), as the search runs.

The consumers are:
- **The CLI session.** It prints invariant, action-property and deadlock traces: the `Violation`'s
  `states` and `labels` go straight into `rebuild`. It prints liveness lassos from the path,
  `lasso_actions` and the loop start. It formats each value with `format_value` and pretty prints
  it.
- **The engine-gaps session.** It maps the engine's stop reasons to a `Site` (an invariant, an
  action, the initial predicate, a constraint) and prints `Failure` as TLC prints it. The message
  texts live here, since they depend on how each value was built (option A, agreed with that
  session).

A search that ranked strings at run time (ToString, #51) hands over no state, so `rebuild` never
meets a store whose string ranks differ from the IR's. A string the evaluator makes that has no
rank is compared by its units, as the store compares it. Where that order could differ from
TLC's, `rebuild` returns `Unsupported`.

## Pull requests

1. `docs(native)`: this plan.
2. `feat(native)`: the crate. It holds the values, their order, `format_value`, the expressions,
   the actions and `rebuild`, for traces without VIEW or SYMMETRY. Its unit tests rebuild traces
   of specs from the corpus and compare them with the interpreter's text. Anything not covered
   returns `Unsupported` and stays not native.
3. With the CLI session: the binary prints traces through `rebuild`. The `tlc/native` count
   before and after goes here.
4. `evaluate_failure`, for the engine-gaps session's errors that print values (about 22 models).
5. ALIAS (the IR has to carry it), VIEW and SYMMETRY (matching through the view or the
   canonical state), and the second rebuild's Print output.

## Parity

The measure is the differential's `tlc/native` pair (`scripts/differential.ts --native`):
the runs, of 1466, whose native transcript equals TLC's. This file records the count before and
after each pull request.

## As built

### The crate (`tla-trace`)

- **Values** (`value.rs`, `sets.rs`). Each function keeps its class, its written order (the
  position of each key written, until a comparison, an equality or a fingerprint sorts it), and
  the interval it was built over, which DOMAIN gives back (`getDomainInterval`). Order,
  equality and membership follow the store's `compare`, `equals` and `is_member`, including where
  they fail. `from_store` reads a store's value as TLC holds it normalized, and `matches` compares a
  value with an id of the store without interning.
- **Expressions** (`eval.rs`). Names resolve as the compiler resolves them, and instances' scopes
  are bound as `context_from_scope` binds them. An operator's argument is evaluated where it is
  used. A function that a definition or a LET defines is applied without being built, so a
  recursive one over `Nat` works. A zero-arity definition that reads nothing of the state is
  evaluated once, as TLC evaluates a constant definition. The builtins are the ones the engine
  implements: logic, sets, integers, sequences, `:>`, `@@`, Assert, Print, PrintT, ToString,
  TLCEval, `TLCGet("level")` and Permutations. Anything else is `Unsupported`.
- **Actions** (`action.rs`). The walk follows `walker.rs`. It assigns at the first `x' = e` or
  `x' \in S`, tests elsewhere, walks UNCHANGED variable by variable, treats `[A]_v` and `<<A>>_v`
  as TLC does, and evaluates the rest of a conjunction as guards once every variable is assigned.
  It binds the bounds of a quantifier as TLC's `ContextEnumerator` does: every set first, then the
  first bound varying fastest. It walks `\A` as the conjunction of its body over the bindings, the
  first and then the others in reverse, as `getNextStates` queues them.
- **Matching** (`rebuild.rs`). Without VIEW or SYMMETRY, a candidate is the state when it equals
  the search's state. Under VIEW, its view must equal the view of the search's state. Under
  SYMMETRY, some permutation of the group must map it to that state, so the two are in one orbit.
  Under both, the views of their least states in the orbit must be equal (`TLCStateMut.fingerPrint`).
  A violation's last state is matched by its value, as TLC holds it (`getTrace` with the last
  successor). Every state but the last is settled as `settleRecoveredState` settles it: fingerprinted
  without VIEW or SYMMETRY, deeply but for lambdas under SYMMETRY, and as `deepNormalize` with the
  view deeply under a VIEW. So is the last one if
  it satisfies the CONSTRAINTs and ACTION_CONSTRAINTs, as TLC fingerprints only such a state.
  A violating last state outside them goes through TLC's checks of it instead, which sort what
  their comparisons reach: the invariants in order until one fails, then the action properties
  (`doNextCheckInvariants`, `doNextCheckImplied`).
  For a plain match where nothing prints, the walk drops an assignment as soon as it differs from
  the search's state. The check sorts nothing, so it changes no value TLC prints, and a model such
  as MCBakery's ISpec doesn't enumerate its 1.7 million initial states again.
- **Enumeration order.** The walks enumerate every set in TLC's normalized order. TLC streams a
  `\cup`, a UNION, SUBSET and the sets of functions, records and tuples in orders of its own
  (`compile/lazy.rs` in the engine). The state the evaluator finds doesn't depend on that order
  without VIEW or SYMMETRY, since it equals the search's. Under VIEW or SYMMETRY, the walk goes
  on past the first candidate that matches. Each walk records the choices it made: the branch of
  each disjunction and the element of each enumeration, and whether TLC takes that enumeration in
  normalized order too (a set enumeration, an interval, a current variable, a constant or a value
  computed at startup). Where two different candidates match, the first is TLC's when their
  choices first part at such an enumeration; otherwise `rebuild` returns `Unsupported` rather than
  guess. What a spec
  prints while TLC enumerates such a set may come in another order; porting the streaming orders
  is left.
- **Print.** Where the spec prints, each walk runs to its end, and each step tries TLC's actions in
  order, as `findStepAction` does. What the walks print is composed as `toTrace` composes it.
  Elsewhere a walk stops at the state it looks for.

Tests:
- every golden IR's search, stopped partway, rebuilds the paths to its last states, VIEW and
  SYMMETRY models included;
- the deadlock traces of kafka_transactions (records) and TLCGetLevel (`TLCGet("level")`) print
  TLC's recorded text, whitespace aside;
- unit tests on the printer and on written order.

### Failures (`failure.rs`)

`evaluate_failure` replays the failure as TLC's `CallStackTool` does, which `tlc/replay.ts` and the
tracing evaluator of `evaluate.ts` port. While it replays, the evaluator keeps a call stack:
- each node `evaluate` evaluates;
- each node the walk visits, as `visit` and `visitUnchanged` do;
- each prefix of an infix chain of junctions, which SANY nests as a node of its own. Its range
  comes from the IR's prefix ends (IR 9).

The successors are replayed for each of TLC's actions: the IR's, or, where the IR has none (as for
a spec that prints), the next-state relation split as `Tool.getActions` splits it. Each disjunct,
the body of an operator whose arguments evaluate without the state, a LET's body and `\E` at each
binding is an action. The first failure freezes the stack. The walk takes TLC's shortcut past assigned conjuncts only in
the initial predicate, and in an action with warnings on, as `isAssignedShortcut` does; that also
decides which frames a stack keeps. The report follows `getFailureMessage`:
- an EvalException that escapes the next-state computation keeps its own code;
- any other error there is TLC's unexpected RuntimeException;
- in the initial predicate the code is the general one, and the -tool text marks the coded message
  inside it;
- an invariant that fails to evaluate past the initial states has the headline "Evaluating
  invariant Inv failed." (2111) and no call stack. Its successor is held as found, as a violating
  one is. On an initial state TLC reports it otherwise, which returns `Unsupported` so far.

An error has TLC's message only where its kind is ported. So far:
- a mistyped membership in Nat, Int or STRING (2158);
- Assert (2132);
- a field selected from a record that lacks it, from a tuple or from a value that isn't a
  function, worded as `getFieldSelector` words it;
- a function applied outside its domain, worded by its class (`describeMissingArgument`);
- a variable read before the state assigns it (2280, `createUnassignedError`), with the range of
  the name read.

A lambda has no message yet: TLC keeps a function constructor lazy only where it evaluates it so
(`EvalControl.KeepLazy`), which the evaluator doesn't follow. A model for TLC 1.7.4 returns
`Unsupported`: that version streams a quantifier's lazy bounds rather than enumerating them in order,
and words some messages apart.

TLC reports a failure in a method of a value with a source (a set, tuple, record or function set
the replay built, or a `\cup`, `\cap` or `\`) as a FingerprintException, with the values'
sources. The replay marks it, as `freezeCallStack` finds it, and returns `Unsupported` for it so
far. Every other failure returns `Unsupported` too. The pretty printer
moved here from the CLI, since the messages need it.

Tests: `tests/failure.rs` runs the engine's search on golden IRs of TLC's own tests (etest9, 10 and
11, AssertExpressionStack, Github461 and EvaluatingValueTest) until it stops, and compares the
message and the call stack with TLC's text.

### Parity

The crate isn't wired into the binary in this pull request, so on main `tlc/native` is unchanged.
On a scratch branch that wired `rebuild` into the CLI's violation and deadlock traces (as of
`native-deadlock-traces`), the Depot differential (all 1466 runs, `depot-ubuntu-24.04-16`) gave
**652** runs that print what TLC prints with the store's printer and **692** with the evaluator.
No run printed anything that differs from TLC's text. With the evaluator, the deadlock traces
still not native fell from 46 to 16 and the invariant traces from 22 to 12. What is left of them
is outside the evaluator:
- an ALIAS (the `_anim` specs, Github746, ViewMap), which the IR doesn't carry;
- a POSTCONDITION;
- traces the engine hands over no violation for, as where it can't label a step (ACP_NB_WRONG,
  the raft specs);
- one ENABLED (spectacle's Elevator).
