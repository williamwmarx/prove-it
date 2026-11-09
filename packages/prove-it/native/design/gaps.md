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
