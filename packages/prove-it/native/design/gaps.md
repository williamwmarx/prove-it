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
- With them, function_syntax (tla-rs), declined before, now completes in Rust. test45 (TLC's
  tests) now searches in Rust until a function construction in a recursive body applies the
  function to itself, which needs the construction to stay lazy as TLC keeps it.
