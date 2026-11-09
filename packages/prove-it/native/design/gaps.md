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

## Parked: TLC registers

- The branch tlc-registers has TLCSet and TLCGet in the Rust search: IR and ABI 9 carry the
  registers, startup registers included, and the search hands them back with a checkpoint or
  when it completes. It gains no model: Test2, TLCGetNonDeterminism and NQSpec check a property,
  and under a liveness graph TLC evaluates the actions again. ConstantContextTLCCache would also
  need TLCCache's cache, which the interpreter fills while it evaluates the assumptions.

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

## Filters of infinite sets

- TLC tests membership in `{x \in S : p}` for a set S it can't enumerate, such as Nat or
  `Seq(S)`, by S's membership and then p (`SetPredValue.member`), and fails where something
  enumerates it. The engine declined any such filter. It now compiles one to that membership test,
  marked infinite as S is, and stops where it is enumerated, which the interpreter reports.
  Community Graphs' `Path(G) == {p \in Seq(G.node) : ...}` is one. MCEWD687a (Examples) and
  Bakery (spectacle), declined before, now search in Rust until the enumeration TLC reports.
