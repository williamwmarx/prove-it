# The native engine's gaps

What the native engine now does where it declined or stopped, as built: one section per change,
newest last. DESIGN.md holds the plan; this file holds how each gap was closed.

## Tuple patterns in an action's `\E`, and Permutations

- **`\E <<a, b>> \in S` in an action** binds each element of S as a set map's tuple pattern does
  (`assign_bound`), the first bound varying fastest as in TLC's `ContextEnumerator`, and stops
  where an element isn't a tuple of the pattern's length, which TLC reports. The TypeScript engine
  still refuses it, so the native engine searches spectacle's simple_quant2 and simple_quant_tuple
  where it hands them over.
- **Permutations(S)** is normalized: `TLC.Permutations` makes a `SetEnumValue`, which TLC
  normalizes before it enumerates, so `\E p \in Permutations(S)` and `x' \in Permutations(S)`
  take the store's order (spectacle's quicksort).
- A function of one bound takes a tuple pattern too (`[<<i, j>> \in S |-> e]`): it binds each
  element's components and keeps the element as the key, as TLC does. AsyncGameOfLife_anim
  (spectacle) now completes in Rust. A function of several bounds with a tuple pattern still stops.

## Lazy UNION

- **UNION S** that TLC keeps lazy (`UnionValue.union` combines S at once only when S and its
  elements are set enumerations) now has a reference, `Lazy::Union`, so the native engine
  enumerates it where the TypeScript engine refuses it. It streams each set of S in turn, in the
  order S streams, duplicates and all (`UnionValue.Enumerator`, the interpreter's
  `streamElements`), enumerates the normalized union (`toFiniteSet`), and tests membership in any
  set of S (`isElementOf`).
- The engine holds S's elements as ids, so it streams each as its normalized set. That is TLC's
  order unless the element itself streams apart (`isStreamedApart`: a UNION or `\cup` TLC keeps
  lazy, or a set built from one). So `Compiled` now says whether a set is known to stream in order
  (`is_in_order`) and whether each of its elements is (`are_elements_in_order`). Both are false
  unless the compiler knows: set enumerations, set maps, intervals, SUBSET and unprimed variables
  outside the initial predicate are in order, and IF, filters, set operations and sets of functions,
  records and tuples are in order when their parts are, a lazy `\cup` never. A UNION over anything
  else, such as a set map whose body is a bound name, or a set of functions over one, still has no
  reference and is refused.
- With it, RealQuicksort and RealQuicksort2 (TLC test-model/pcal), declined for
  `UNION {[1..N -> 1..N] : N \in 0..MaxLen}`, complete in Rust with output identical to TLC's.
- The model's constants are the values its configuration writes, which TLC normalizes, so a
  constant and each set in it are in order too. MCBinarySearch and MCQuicksort (LoopInvariance),
  which enumerate `UNION {[1 .. n -> S] : n \in 1 .. MaxSeqLen}` over the constant `Values`, now
  complete in Rust. A value TLC computed at startup still isn't, since TLC may keep it lazy;
  neither is an instance's substitution nor DOMAIN of a primed variable, which still decline
  ClientCentricTests (mongodb-txns) and test46.

## ToString

- **ToString** (`compile/builtins.rs`) gives TLC's text of its argument (`tla_values::print`,
  `formatValue(v, true)`), and ranks the string it makes, as `rankString` does. It stops where
  the text depends on how TLC built the value, which the store forgets (`is_printable`), as Print
  and PrintT do.
- **The search never orders the strings it ranks.** TLC ranks a string as it makes it, and the
  engine may make ToString's strings in another order: across successors it pipelines, where it
  builds every entry of a function TLC applies lazily, or for a text `\o` made earlier, which
  the store keeps unranked. So the store freezes TLC's order when the search starts
  (`freeze_string_order`), and comparing a string ranked since with another string stops the
  search. A search that ranked strings hands over none of its states, so the interpreter makes
  them again from the start, in TLC's order. Starting over would print again what the search
  printed, so a model that prints and uses ToString declines.
- With it, the native engine declines no corpus model the TypeScript engine searches:
  simple_strings and UnicodeStringDiskStateQueue, the two it declined for ToString, now search in
  Rust until the stop the TypeScript engine reaches. The other 49 it declines (TLC under 20 s) the
  TypeScript engine refuses too, for the same reason.

## Action composition

- TLC fails on `A \cdot B` wherever it reaches it, in the next-state relation, an expression or
  ENABLED (`Tool.java`), unless a Java property enables its incomplete implementation. The
  engine compiles it to an expression that stops the search when evaluated, with the states
  found before it, and the interpreter reports TLC's error from there. Both engines declined
  the five cdot models in TLC's tests before; the native engine now searches them until the stop.

## `_POSSIBLE` predicates

- TLC counts each `_POSSIBLE` predicate on every state the state constraints keep, duplicates
  included, and each action-level one on every step the action constraints keep
  (`trackPossible`). It reports one that never held, with the counts, after the search. The IR
  (version 7) carries the predicates, each with whether it is of a step. The search counts them
  where the interpreter does, -1 until one is evaluated. It hands the counts over with a
  checkpoint as they stood before the expansion the interpreter goes on from, or the final counts
  when it completes. The addon (ABI 8) passes them as `possible`.
- Only the native engine counts them, so a model with `_POSSIBLE` predicates goes to the
  interpreter where the native engine doesn't take it, never to the TypeScript engine. The search
  stays on one thread with them.

## `SUBSET A \subseteq SUBSET B`

- TLC compares two power sets by their bases, without building either, unless it can't enumerate
  A (`SubsetValue.isSubsetEq`), and does so again for power sets of power sets. `SUBSET` records
  its base (`Compiled::subset_base`) for `\subseteq` to compare in its place. SubsetEq (TLC's
  tests), which stopped building `SUBSET (1..42)`, now completes in Rust. The interpreter doesn't
  recurse into power sets of power sets, so the unit test leaves that case out.

## Wide strings

- TLC fingerprints a string by the low byte of each character and tells states apart by their
  fingerprints alone, so states whose strings differ only above U+00FF are one state. The native
  engine does both already (`fingerprint.rs`, `States::find`). Only the TypeScript engine tells
  states apart by their values, so a model whose strings may be wide (`hasWideString`) goes to the
  native engine, or to the interpreter where it doesn't take the model, never to the TypeScript
  engine. Resuming from a checkpoint, the interpreter then takes every state over at once, since it
  tells them apart by fingerprint and the checkpoint looks a state up by its key.

## TLCModelValue

- **TLCModelValue(s)** gives the model value named s, which TLC makes once per name and ranks
  the name as it makes it (`TLCExt.tlcModelValue`, `ModelValue.add`). So it ranks as ToString
  does: the search stays on one thread, one that ranked a name hands over none of its states, and
  comparing a model value whose name it ranked stops, as comparing such a string does. It stops
  where s isn't a string, which TLC reports. Github696 and Github696b (TLC's tests),
  declined before, now search in Rust until the comparison of differently typed model values
  TLC reports.

## Values computed at startup

- TLC computes each constant definition once when it starts (`SpecProcessor.processConstantDefns`),
  one with effects such as RandomElement included, and reads that value from then on. The IR
  carried the value for a definition with effects only when it was a string, number or boolean,
  and the native engine declined any other. It now carries any value the interpreter holds settled
  (`isSettledValue`), which TLC doesn't keep lazy, so the search reads it in place of the
  definition. One TLC may keep lazy, such as SUBSET or `\cup`, still declines. Github648 (TLC's
  tests) now completes in Rust.

## RandomElement and RandomSubset

- TLC draws from one java.util.Random per thread (`RandomEnumerableValues`): the main thread's
  for the assumptions and the initial states, and in a worker one it reseeds with the fingerprint
  of each state it expands, xored with the seed. So a state's successors draw the same whatever
  thread expands it. The IR (version 10) carries the seed and the state the assumptions left the
  generator in. The search draws from that for the initial states and reseeds for each expansion
  with the fingerprint it found the state by (`Machine::seed_random`). `compile/random.rs` ports
  java.util.Random and the draws of `tlc/random.ts`: RandomElement draws each component of a set
  of functions, records or tuples in turn, and RandomSubset draws indices from TLC's linear
  congruential generator, of an interval by its bounds and of a product by its index, as TLC 1.7.4
  or master does.
- Both compile where Print may print, since a draw depends on how many draws came before it, so
  the search stays on one thread and evaluates them as TLC does. Elsewhere they decline: as an
  operand of `\subseteq`, as in RandomSubsetNext, and where a liveness graph evaluates actions
  again.
- A trace the interpreter rebuilds after a hand-over now draws as TLC's does (`TLCTrace#getTrace`):
  each initial state from the generator the search started with, and each successor from one
  seeded with its predecessor.
- TLC labels each step of a trace as it rebuilds the trace, with a generator it resets first, so
  it reseeds for each predecessor. The checker finds a step's action by evaluating the actions
  again, so it now resets the generator first (`resetRandom`). Before, a step whose predecessor
  the generator was last seeded for drew on from where it stopped, and the step lost its label.
- RandomElement, RandomElementXandY, RandomSubsetNextTuples and RandomSubsetSetOfFcns (TLC's
  tests), declined before, now search in Rust, and RandomSubset until its invariant builds
  `1..100000000`.

## TLC registers

- TLCSet and TLCGet of a number or of a name that starts with "s:" run in the Rust search as TLC
  runs them on one worker (`TLCGetSet`): a register TLCSet sets at startup, in an assumption,
  holds for the search. TLCSet is an effect, so like Print it compiles where the engine evaluates
  as TLC does, and nothing caches what reads a register. The search hands the registers on with a
  violation, whose trace `tla-trace` rebuilds setting them again as TLC does, and once it
  completes, for the postconditions, which read `TLCGet("all")` and the named registers in
  `TLCGet("all:named")`.
- TLCCache evaluates its expression once for each key where the expression reads no variable
  (`TLCExt.tlcEval2`), by the expression's node, and TLCFP is the low 32 bits of the fingerprint
  of a state of its value alone. TLCGet("config") is the record `AbstractChecker.createConfig`
  makes, TLCGet("spec") the record the interpreter computes, which the IR holds where an
  expression reads it: tla-front describes the specification as `getSpecDescription` does
  (`describe.rs`), and `tla-trace`'s split gives its actions (`add_spec`), as the native binary
  lowers the model; the TypeScript front end's model, as `model-full` compares it, has neither. And
  TLCGet of a Java property its key. The other keys of TLC's run, and the diameter outside the
  liveness checker, stop the search where TLC would read them, once TLC has started, as an
  assumption may stop TLC first.
- Only the native binary takes them: the interpreter would take a search over without the
  registers, so the engine declines them under the TypeScript engine.
- Still declined: an atom of the liveness checker that sets or reads a register, since TLC
  evaluates the atoms as it adds each state to the behavior graphs (TLC's Test2 counts them), and
  the keys that stop, pause or configure TLC. TLCFP and TLCCache don't evaluate in `tla-trace`
  yet.

## Functions of several bounds, and recursive functions TLC keeps lazy

- **A recursive function of several bounds**, such as `add[a \in A, b \in B]`, is TLC's function
  over `A \X B`. Its argument is a tuple in one slot, each name is its element of the tuple, and
  `add[a, b]` applies it to `<<a, b>>`. A bound with a tuple pattern still declines.
- **A function construction of several bounds** binds a tuple pattern at any level
  (`assign_bound`), as `[a \in S, <<b, c>> \in T |-> e]` does, where it stopped before.
- TLC keeps a recursive function lazy (`FcnLambdaValue`). So an operator's argument that names
  one applies it where the operator applies the argument, and DOMAIN of one is its domain. Before,
  the engine built it, which a domain such as Nat stopped, and a body that reads its own DOMAIN
  never finished.
- With them, function_syntax (tla-rs), declined before, now completes in Rust.
- TLC keeps a function construction lazy too, so `f[i \in S] == [j \in T |-> e]` applied as
  `f[a][b]` evaluates e for b alone, and e may apply `f[a]` to another element. The engine built
  `f[a]` whole, which recursed forever where e applies it. Where a recursive function's body is a
  function construction, `f[a][b]` now calls a runtime of its own for e, with a and b bound and
  each checked against its domain, as `FcnLambdaValue.apply` checks them. test45 (TLC's tests)
  now completes in Rust.

## Filters of infinite sets

- TLC tests membership in `{x \in S : p}` for a set S it can't enumerate, such as Nat or
  `Seq(S)`, by S's membership and then p (`SetPredValue.member`), and fails where something
  enumerates it. The engine declined any such filter. It now compiles one to that membership test,
  marked infinite as S is, and stops where it is enumerated, which the interpreter reports.
  Community Graphs' `Path(G) == {p \in Seq(G.node) : ...}` is one. MCEWD687a (Examples) and
  Bakery (spectacle), declined before, now search in Rust until the enumeration TLC reports.

## Membership in an interval

- TLC tests `x \in a..b` by comparing an integer with the bounds (`IntervalValue.member`), and
  fails on any other value but an untyped model value, which isn't a member. Membership in
  `..` (`member_test`) now does the same, where the engine built the interval to look the element
  up, and stopped on one too large to build, such as RandomSubset's invariant
  `x \in 1..100000000`. Elsewhere the interval is as before, so a set operation or a set of
  functions over one still evaluates it, and its bounds, as TLC does.

## Definitions reached again through an argument

- Both engines took a definition they reached again while expanding it for recursion, and declined
  it as "a recursive higher-order operator". A definition is also reached again through an
  argument, as mongodb-txns' ClientCentric folds in the operator it passes to Community Modules'
  FoldFunction, which is no recursion: SANY rejects a definition that calls itself without
  RECURSIVE. The definitions being expanded now travel with the context (`expanding`), so an
  argument compiles with those of the place it is written, and only a cycle through definitions
  is taken for recursion. ClientCentricTests and MCMultiShardTxn (mongodb-txns), declined before,
  now search in Rust, and the TypeScript engine searches them too.

## The order UNCHANGED evaluates in

- TLC evaluates `UNCHANGED e`, `[A]_e` and `<<A>>_e` in the current state before the next one
  (`Tool.evalAppl`, `verifyUnchanged`), so where both sides fail it reports the current state's
  failure. The interpreter (`codegen.ts`, `evaluate.ts`) and both engines' UNCHANGED evaluated the
  next state's side first; each now evaluates the current state's first. The engines' `[A]_e` and
  `<<A>>_e` already did.

## A value substituted for an operator with parameters

- A configuration may substitute a value for an operator with parameters, as mongodb-txns'
  Storage.cfg substitutes FALSE for its actions. TLC applies the operator by taking the value,
  without evaluating the arguments (`Tool.evalAppl`), so `A(1 \div 0)` under `A <- FALSE` is FALSE
  (checked with TLC 1.8.0). The interpreter evaluated the arguments and failed on them, and both
  engines declined the builtin applied to arguments. All three now take the value. Storage
  (mongodb-txns), declined before, now searches in Rust, and the TypeScript engine searches it too.

## A primed variable a LET names

- TLC's `getPrimedVar` looks through a LET and a label to the primed variable an `=` or `\in`
  assigns, so `(LET y == x' IN y) = 0` assigns x', in the next-state relation and in ENABLED.
  Both engines' walkers stopped at the LET and declined it as "an assignment the engine can't
  resolve statically". They now bind the LET's definitions and look through it, and through a
  label. Github725d (TLC's tests), declined before, now searches in Rust, and the TypeScript
  engine searches it too.

## SUBSET of a set with no order

- TLC enumerates `SUBSET S` in the normalized order of S's elements, whatever S's own order
  (`SubsetValue.elementsNormalized`). Both engines enumerated a power set only where its base had
  an order of its own, and declined `x' \in SUBSET S` for any other S as "enumerating a set TLC
  keeps lazy". The power set now enumerates its base's value in that order. test46 (TLC's tests),
  declined before, now searches in Rust, and the TypeScript engine searches it too.
- Comparing the results in full, where the native engine stops on a violation whose trace holds
  sets of records, the interpreter's trace marks a record as fingerprinted and the native engine's
  doesn't. What either prints is the same.

## Where the search stops on a failure

- The search stopped on a failure evaluating the model, such as an Assert or a value of the wrong
  kind, with only its reason, so the binary left the model to the interpreter. It now reports the
  stop as a violation, `ViolationKind::Error { site }`: in the initial predicate with no states,
  in the next-state relation with the path to the state it was expanding, or in invariant n with
  the path and the successor that failed it, with TLC's counts. That is what
  `Rebuilder::evaluate_failure` takes (`tests/stops.rs`), and the binary prints TLC's report from
  it. A stop at one of the engine's own limits (`is_engine_limit`) stays a stop with no
  violation.
- Labelling a path where the engine has no walk of TLC's actions leaves its steps unlabelled,
  where it panicked on a path of one step.

## A power set TLC can't count

- TLC counts a power set's elements in an int, so it fails counting those of SUBSET S where S has
  31 elements or more (`SubsetValue.size`), which it reports, wrapped in a FingerprintException
  where it fingerprints the set. The engine stopped at its own limit on building a power set, and
  such a stop isn't a failure TLC reports. It now fails on a base of 31 elements or more as TLC
  does, and stops at its limit only below that. FingerprintExceptionInit and
  FingerprintExceptionNext (TLC's tests) now stop on that failure in Rust.

## An operator the configuration defines by its values

- A configuration may define a constant operator by its values, `F(0) = 1`, which TLC applies by
  the row whose arguments equal the arguments and fails to apply outside its rows. The IR carried
  the operator as a builtin of that name, which the engines didn't know. A builtin now carries
  such a table (`Builtin::TABLE`): its rows, each its arguments as a tuple and its value. The
  native engine applies it, and fails outside its rows as TLC does; the TypeScript engine applies
  it as the interpreter does. ConstantOperatorConfiguration (TLC's tests), declined before, now
  searches in Rust, and the TypeScript engine searches it too. The Rust front end lowers no table
  yet (`tla-front`'s `get_builtin_index`).

## Recursive functions an instance or an operator gives

- `f[n \in S] == ...` defined in an instanced module, or returned by an operator as
  `LET s[n \in Nat] == ... IN s`, is applied as TLC applies it, through its recursive definition.
  The engines found a recursive function only by an identifier in scope, so they declined
  `I!f[3]` and `Scaled(2)[3]`. They now see through LET, an applied operator and an instance's
  definition to the function, and bind its name to itself in a scope kept per definition.
  function_instance (TLC's tests), declined before, now searches in Rust.

## A recursive function an action applies

- TLC walks the body of a function it keeps lazy where an action applies it (`getNextStates` on
  `FcnLambdaValue`), a recursive function's body too, so each path through its `\/` and `\E` that
  holds goes on with the rest of the action and makes a successor. A body that applies the
  function again recurses as the search runs, which a walk compiled path by path can't unroll.
  The engine declined it. The body's walk is now compiled once for what the walk knows where the
  action applies the function, and each application runs it a level deeper with a continuation
  that puts the caller's slots back and goes on with the rest of the walk. A body that assigns a
  variable still declines. VoteProof (Examples, and TLC's tests), declined before, now searches
  in Rust: `SafeAt`'s `SA[b]`.

## The out-degrees after an invariant fails to evaluate

- After an invariant that fails to evaluate, TLC prints the state graph's out-degrees: those of
  the expansions it completed, and the one it was running, counted with the new states it had
  found, the failing one included (TLC counts a new state before it checks the invariants). The
  stop (`ViolationKind::Error` at `ErrorSite::Invariant`) now carries them in
  `StopCounts::out_degrees`; other stops leave them empty.

## A failure on an initial state

- TLC evaluates the constraints and the invariants on each initial state as it computes the
  initial states (`DoInitFunctor`), and reports a failure there with the state ("While working on
  the initial state") and the counts so far, the state counted as generated. The engine reported
  it as a failure in the initial predicate, without the state. It now stops at
  `ErrorSite::InitialConstraint(n)` or `ErrorSite::InitialInvariant(n)`, n the position in the
  model's constraints or invariants, with the state as the violation's one state and TLC's
  counts: 1/0/0 at depth 1 on DoInitFunctorEvalException and 1/1/1 on
  DoInitFunctorMinimalErrorStack. The CLI leaves both to the interpreter until it prints them.
- TLC checks its implied inits, the state predicates of the properties, of each initial state
  after the invariants (`getImpliedInits`). A failure there, as cdot/CdotWithContextB's
  `Prop2 == ENABLED Next` reaching `A(n) \cdot B(n)`, now stops at
  `ErrorSite::InitialPredicate(n)`, n the position in the IR's `model.initial_predicates`, with
  the state and TLC's counts (1/1/1 at depth 1).

## An assumption that fails to evaluate

- TLC reports an assumption that fails to evaluate at startup (2105, "Evaluating assumption ...
  failed."), after what the startup and the assumptions before it printed. The engine declined
  the model. Where the search reports violations (`Settings::is_violation_reported`, as the CLI
  sets it), it now reports what the startup printed and stops with
  `SearchOutcome::AssumptionFailed { position }`, the position in the IR's assumptions; a failure
  that is the engine's own limit still declines. Elsewhere it declines as before, so the
  interpreter, which checks the assumptions itself, prints nothing twice. The CLI leaves it to
  the interpreter until it prints it.

## A function a definition gives, applied in an action

- `N[n \in S] == UNCHANGED <<x>>` applied in an action as `\E i \in S : N[i]` is a FcnLambdaValue
  TLC walks as an action (`getNextStates`), so `x'` is assigned. The engine walked only a function
  a construction or a LET gives, and evaluated a definition's, so it stopped on "primed variable
  not assigned" where TLC completes. It now walks the body of a function a definition gives too,
  a recursive one included, unless TLC evaluated the definition at startup. coverage/I (TLC's
  tests) now completes in Rust: 20 states generated, 5 distinct, as TLC.

## A universal quantifier in the initial predicate

- TLC walks `\A` in `getInitStates` whatever its body, so `\A v \in {2} : s = v` assigns s for the
  first binding and tests it for the others. The engine walked `\A` only where its body has a
  prime, UNCHANGED, `\/` or `\E`, and evaluated `s = v` as a guard while s had no value: it
  stopped on "variable not assigned" where TLC finds the state. Its check of a body now also finds
  an initial predicate's unprimed assignments, `x = e` and `x \in S`.
- TLC computes the initial states building a function at once (`EvalControl.Init`), all but a
  recursive one, so it applies a function's value there rather than walking its body. The engine
  walked the body of a function a construction gives where it branches; in the initial predicate
  it now walks only a recursive function's body. AssignmentInit (TLC's tests) now stops at the
  deadlock in Rust, as TLC.

## Which stops are TLC's failures

- The search reports a stop as a failure TLC reports (`ViolationKind::Error`,
  `AssumptionFailed`) unless the reason is the engine's own limit. It listed the limits, so a
  reason it didn't list, such as a decline that a compile defers to run time ("printing a value
  whose text depends on how TLC built it"), was reported as TLC's failure: FastMutex2 and
  FastMutex3 reported assumptions that hold in TLC as failing. It now lists the reasons that are
  TLC's failures (`TLC_FAILURES` in `search.rs`), and every other reason is a limit, so a reason
  it doesn't know falls back to the interpreter. Enumerating an infinite set is a limit too: the
  engine enumerates Nat where TLC keeps the set lazy, as on suite/test202's and
  RandomSubsetEmpty's assumptions, which hold in TLC.
- Comparing a record with a function fails in TLC only where it built one value as a record
  (`RecordValue.equals`); a function a constructor builds over strings is a FcnRcdValue, which
  compares its domain with any function's. The store, which merges equal values, knows a value by
  its domain only, so it can't tell the two: tla-rs model_values_distinct compares
  `[n \in Node |-> "idle"]` with `[n \in {"n1", "n2"} |-> "idle"]` and gets FALSE in TLC, where
  the engine stopped. "record compared with a function" is now a limit, which the interpreter
  takes over from; following it natively needs the store to keep how TLC built a value.

## Len and Tail of a string

- TLC's `Sequences.Len` and `Sequences.Tail` take a string too: its length in UTF-16 units, and
  the string without its first unit, failing on the empty string as on the empty sequence. The
  engine expected a sequence and stopped with "expected a sequence", which suite/test60's
  assumptions reported as failing where they hold in TLC. Both now take a string.

## A recursive operator TLC walks

- TLC walks a RECURSIVE operator's body where the initial predicate or an action applies it, as
  any operator's: coverage/Github649's `Init == Flip(clock, FALSE, 1)` assigns clock two calls
  down. The engine can't unroll a recursive operator as it compiles the walk, and evaluated the
  call as a guard, so it stopped on "variable not assigned", a failure TLC doesn't report.
- Where the operator's body is one the walk would go into, the walk now recurses as it runs
  (`walk_recursive_operator`, `WalkedOperator`), as a recursive function's does. The body's walk
  is compiled once for the operator, what the walk knows where it is applied, and the variables
  its arguments name: an argument that names a variable, primed or not, stays the compile-time
  binding, since it decides what the body assigns, and the others are evaluated into the
  parameters' slots at each call, as a recursive operator's are in an expression. A conjunction
  takes such a call for a walk too, where it took it for a guard.
- The body may assign, which the compiler doesn't follow through the recursion, so the rest of
  the walk after a call knows only what was assigned before it (`Known::opaque`). A body that
  applies itself knowing more each level compiles for nothing known past a few.
- Declined: an argument that names variables but isn't one, such as a tuple of them or a LET
  ("walking a recursive operator whose argument names variables indirectly"), and an operator
  parameter. `\A` and a lazy function's body don't look through a recursive operator to decide
  whether they are walked (`has_walk`), so one that assigns only inside such a call is a guard
  there, which stops on a limit.
- Github649 (TLC's tests) now completes in Rust and prints what TLC prints.

## UNCHANGED of a tuple that isn't all variables

- TLC goes through UNCHANGED of a tuple element by element (`processUnchanged`): it assigns a
  variable and compares anything else's values in the two states. Github702's instance
  substitutes a constant for x in `UNCHANGED <<x, z>>`. The engine walked UNCHANGED only of a
  tuple of variables, and evaluated any other whole as a guard, where z' had no value: it stopped
  on "primed variable not assigned". It now walks such a tuple element by element, and follows
  an operator's argument, as the interpreter does; a global definition is still evaluated whole,
  as the interpreter evaluates it. Github702 (TLC's tests) now completes in Rust: 36 states
  generated, 30 distinct, as TLC.

## Functions TLC keeps lazy

- TLC keeps a function construction over a set it can't enumerate, such as `[n \in Nat |-> e]`,
  as a `FcnLambdaValue`. The engine now does the same (`compile/lazy_function.rs`). It is a store
  value of its own kind (`KIND_LAZY_FUNCTION`) that indexes `Machine.lazy_functions`.
- Applying one checks its EXCEPTs, latest first, then that the state is the one it was built in,
  then the key against each bound's domain (`Lazy::contains`). Then it evaluates the body with the
  captured slots and the key bound. EXCEPT, with `@` and nested paths, appends a key and value.
- Comparing, fingerprinting, printing, DOMAIN, and a state holding one are engine limits, as TLC
  can't do them without enumerating the domain.
- The lazy path compiles only where a bound's set may be infinite (`Compiled::may_be_infinite`,
  with `has_infinite_part` for sets built from others). Where it compiles, it turns off pipelining
  and level sharing, since only the machine that built a function can apply it.
- suite/test3, test5, test10, test12, test17 and test202 now print what TLC prints.

## ENABLED in the initial predicate

- TLC evaluates ENABLED A in the initial predicate against the state the predicate has built so
  far (`Tool.eval`, OPCODE_enabled, with the partial state as the current one), as EWD840/MC02
  does, whose specification conjoins `ENABLED Next`, and suite/test216's
  `Thm1 /\ ENABLED Thm1Prime!:`. The engine declined it. It now walks A there as anywhere else:
  the walk reads the variables the predicate has assigned, and stops on its limit ("variable not
  assigned") where A reads one it hasn't. EWD840/MC02 and suite/test216 now print what TLC
  prints.

## A function of several arguments an action applies

- TLC walks the body of a function it keeps lazy where an action applies it, with each name
  bound to its argument once every argument is in its bound's set (`getFcnContext`). The walker
  took only a function of one name. It now binds one slot for each bound, as spectacle
  Elevator's `CanServiceCall[e, call]` needs, and declines only a tuple pattern, an application
  to one tuple (`f[<<a, b>>]`), and a recursive function of several bounds. The decline also no
  longer comes before the check of whether the body is walked at all, so a guard such as
  Elevator's compiles as a guard. Elevator now prints what TLC prints.

## Print under a quantifier

- TLC evaluates the body of `\A` or `\E` for each element in the order it enumerates the set
  (`Tool.contexts`), until one decides the quantifier. The engine now does so for a quantifier
  of one bound whose body prints (`compile_quantifier`): it takes the elements in TLC's order
  (`order`, as the walk of `\E` in an action does), so a set TLC keeps lazy, such as
  suite/test11's `[{1+1, 2} -> {3-1, 2, 1+1}]`, needs a reference, and declines without one.
  Several bounds still decline. Stones (Examples), whose assumption prints the solution under
  `\E`, now prints what TLC prints.

## Print inside ENABLED

- An ENABLED in an expression isn't evaluated as TLC evaluates it (its value is cached by what
  the action reads), so a Print inside it declined the model. ENABLED stops at its action's
  first successor, which often passes no Print: suite/test20's `ENABLED ((x = 1) /\ Next)` finds
  one in Next's first disjunct. A Print inside such an ENABLED now compiles to a stop ("Print
  inside ENABLED", one of the engine's limits) that only evaluating it reaches
  (`decline_print`, `silent_enabled_depth`). The liveness checker's ENABLED atoms, which print
  as TLC does, are as before. suite/test20 now prints what TLC prints.

## A quantifier over a set TLC can't enumerate

- TLC fails where an action quantifies over Nat, or assigns a variable from it ("TLC
  encountered the non-enumerable quantifier bound"). The engine stopped on "enumerated an
  infinite set", which is one of its limits because it enumerates some sets elsewhere that TLC
  doesn't. Where the walk, or a quantifier that prints, takes a set's elements in TLC's order
  (`order`) TLC enumerates the set too, so a set known to be infinite as it compiles now stops
  there with a reason of its own (`INFINITE_BOUND`), which is among TLC's failures. The replay
  (`tla-trace`'s `check_enumerable`) words TLC's message, with its explanation for Nat, Int,
  Real and Seq(S) since 1.7.4. Bakery (spectacle) now prints what TLC prints.

## DOMAIN of a function TLC keeps lazy

- `DOMAIN f` of a `FcnLambdaValue` is its bound's set, or the tuples of its bounds' sets
  (`getDomain`), which TLC only tests. The engine has no value for such a set, so DOMAIN still
  stops as a value, but `x \in DOMAIN f` now asks the function's bounds (`is_in_domain`).
  suite/test11, whose tests ask `5 \notin DOMAIN f1` for `f1[i \in Int]`, now prints what TLC
  prints.

## INSTANCE in a LET, in the replay

- The replay (`tla-trace`) declined any LET with an INSTANCE ("rebuilding a trace: INSTANCE in
  LET"), as the engines did before they took the definitions the INSTANCE copies into the LET.
  It now binds them as the LET's other definitions (`bind_let`). EWD998_anim,
  CabbageGoatWolf_anim and AwsDNSRace_anim (spectacle) now print what TLC prints.

## A failure's trace with an ALIAS

- TLC prints the trace to the state it was expanding through the ALIAS, each state with the one
  after it as its next state and the last with itself, but an initial state it was expanding,
  which is the whole trace, as it is (`TLCTrace.printTrace`). The CLI declined any failure with
  an ALIAS. It now prints one in the next-state relation or an invariant (`failure.rs`), with
  the startup values and registers the alias may read, and still declines the other sites, a
  state TLC fails to fingerprint, an incomplete successor, and any failure with a POSTCONDITION
  or `_POSSIBLE` (cdot/ChainedCdots: TLC checks the postcondition between the trace and the
  call stack, with TLCGet("generated") and the registers as the failure left them). bfs_anim
  (spectacle) now prints what TLC prints.
- A deadlocked initial state is such a trace of one state too: the CLI printed it through the
  ALIAS, where TLC prints the state. It now prints the state.

## A function TLC asks whether it equals a record

- `left = right` is `left.equals(right)` in TLC. A RecordValue fails on a function that is no
  record, but a function with a key that isn't a string is a FcnRcdValue or a tuple, which
  takes any function and compares keys and values (`FcnRcdValue.equals`). The store, which
  can't tell a record from a function over strings, stopped on either order. `=` and `#` now
  ask as TLC does (`Store::equals_asked`): where the left side has a key that isn't a string
  and the right side's are all strings, the keys in order decide, or fail as TLC's do
  (`<<1, 1>> = [a |-> 1, b |-> 1]` compares 1 with "a"). The other order still stops, since the
  left side may be a record. tla-rs model_values_distinct now prints what TLC prints.

## Open: infinite sets as values

These three are declined, and lazy functions don't fix them:

- **suite/test7**, Test 14: `CHOOSE j \in {{Nat}, {Int}} : \E k \in j : -1 \in k` holds Nat and Int
  as elements of a set. TLC keeps them as values and tests membership in them. The engine has no
  store value for a set it only tests, so it declines with "enumerated Nat". This needs a store
  kind like the lazy function's, an infinite set by name, with membership and the comparisons TLC
  makes when it normalizes `{Nat}` and `{Int}`.
- **suite/test9**: `2 \notin {i \in Int : i > 1}` and `<<3,4>> \notin {<<i,j>> \in Int \X Int : j > i}`
  decline with "enumerated Int". A filter compiles to its membership test only where its set is
  marked `infinite` (see "Filters of infinite sets"). `Int \X Int` is a product, marked only
  `has_infinite_part`, so its filter compiles to the enumerating form. Find out whether the
  constant `\notin` of the plain Int filter also goes that way. The likely fix is to key the
  filter's membership form on `may_be_infinite` and use the product's own member test.
- **RandomSubsetEmpty**: `Cardinality` and `RandomSubset` of `[Nat -> {}]`, `[n1 : Nat, n2 : {}]`,
  `Nat \X {}` and the like decline with "enumerated Nat". TLC counts these sets without
  enumerating them. A product or record set is empty when any factor is, and `[S -> {}]` is empty
  for a nonempty S. RandomSubset then picks from none. The spec's comments name the order that
  matters: the empty factor must be found before an infinite one is touched. Cardinality and
  RandomSubset need a size for a lazy set that answers 0 in these cases before they enumerate.

## Open: Test2, liveness atoms answered as the search goes

TLC evaluates the liveness checker's atoms as it finds states, so atoms that print or set
registers do it in TLC's order. The engine answers them in tables after the search, which is why
Test2's output differs. The liveness session's design, open for whoever owns it next:

- `add_states` (tla-live `checker.rs`) is already incremental. It calls `add_initial_state` for
  each initial state, then `add_state(i)` for each state in order. `add_state` reads only what is
  known once i is expanded: its edges, `parents` and `fingerprints`, and `diameters[i]`. Late
  nodes and `Verdict::Unexpanded` come only with SYMMETRY or VIEW (`reals`), which this path can
  decline.
- The obstacle is ownership. `Checker<'c>` borrows the graph and tables for its whole life, so
  the search can't grow them. Preferred fix: pass the graph into each call
  (`add_state(&mut self, graph: &Graph, state)`) and build it once for `check`, `find_accepted` and
  `add_states`, which then keep their signatures.
- Answers move behind an `Answers` trait in tla-live (std only), with the table-backed answers as
  the default implementation. That implementation keeps `position()` and its diameter offset.
  Action answers are indexed by edge position, with stuttering at `edges.len() + state`, and that
  offset shifts as edges grow. So an online provider takes (atom, state, step), or the trait gives
  stuttering steps their own index (`Slot { State, Step, Stutter }`).
- `Liveness::unanswered` must keep working; it gives `ErrorSite::Atom` for Github607. An online
  provider can return the evaluation failure itself instead.
- Evaluate each atom every time TLC does. The `effects` log and the `known` short-circuit assume
  one evaluation per check, so don't cache across checks when an atom has effects
  (`is_effectful` already turns caching off).

## Handoff (gaps session, 2026-11-09)

Done since by the engine-gaps session (each in a section above): the run-time walk of a
recursive operator (Github649), ENABLED in the initial predicate (EWD840/MC02, test216), a lazy
function of several arguments in an action (Elevator), Print under a quantifier (Stones, test11)
and inside ENABLED (test20), a quantifier over Nat as TLC's failure (Bakery), and membership in
DOMAIN of a lazy function (test11), INSTANCE in a LET in the replay (the `_anim` models), a
failure's trace through the ALIAS (bfs_anim), and a function compared with a record
(model_values_distinct). The addon suite's "leaves a model it can't search to the TypeScript
engine" already declines on UNCHANGED in the initial predicate.

Done before that (each in a section above): run-time error stops (ErrorSite Init, Next,
Invariant with out-degrees, InitialConstraint, InitialInvariant, InitialPredicate, and
AssumptionFailed); `TLC_FAILURES`, the list of the reasons that are TLC's failures, every other
reason a limit; operator tables; recursive functions from instances and operators; lazy element
application (test45); the run-time walk of a recursive function (VoteProof); walking a function a
definition gives (coverage/I); `\A` that assigns in Init (AssignmentInit); UNCHANGED element by
element (Github702); Len and Tail of a string (test60); INSTANCE in LET (test59,
CyclicRedefineInstance, EWD998Chan).

Open, with what is known:

- **Github696, AssertError.** Not started; the startup AssertError items went to the platform
  session.
- **cdot/ChainedCdots** (a failure with a POSTCONDITION): the CLI declines it. TLC checks the
  postcondition after the trace and before the call stack (`Worker.doPostCondition`), with the
  registers and counts as the failure left them.
- **RandomSubsetEmpty** still reports AssumptionFailed (trace session, 20:04). Find the bail
  reason (bac5cb17 now lowers a model without a next-state relation, so engine-ir gives its IR);
  it should be a limit if TLC's assumption holds.
- **FingerprintExceptionHang, for the trace session.** After an invariant fails to evaluate, TLC
  replays the expansion and skips each successor already in its fingerprint set. The engine
  never generates the successors after the failing one, so the stop should carry the
  fingerprints found when it stopped (`states.fingerprints`, sorted), and tla-trace, which has
  `tla_values::fingerprint::Fingerprints`, tests each replayed successor against them.
