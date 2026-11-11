# Lazy sets that stream duplicates

TLC counts every state its enumeration of `x \in S` (or `x' \in S`) yields, duplicates included.
Where S is a set TLC keeps lazy, that count depends on whether TLC has normalized the very object
it enumerates. The distinct states never differ; "states generated", the counts printed at a
violation and anything computed from them do. This note gives TLC's rule at d8fb231, what the
engine declines to keep from printing other counts, and what is still wrong.

## TLC's rule

Paths are under `tlatools/org.lamport.tlatools/src/tlc2/`.

- **Which sets stay lazy.** `UNION` merges at once when its set and every element are set
  enumerations (`value/impl/UnionValue.java:215-239`), else it builds a `UnionValue`. `\cup`, `\cap`
  and `\` reduce eagerly when both sides are `Reducible` (`tool/impl/Tool.java:2682-2718`,
  `value/impl/SetEnumValue.java:217-236`, `value/impl/IntervalValue.java:190-207`), else they build
  a `SetCupValue`, `SetCapValue` or `SetDiffValue`. A filter over a lazy set is a `SetPredValue`.
  A set of all sorts as it enumerates (`SetEnumValue.java:295`, `479-481`) and SUBSET normalizes
  its base (`SubsetValue.java:742-756`), so neither duplicates.
- **How a lazy set streams.** Until normalized, its `elements()` streams its operands' elements,
  duplicates included (`SetCupValue.java:259-305`, `UnionValue.java:322-379`); after, it streams
  the cached normalized set.
- **What normalizes it in place.** `convertAndCache` (`SetCupValue.java:209-217`,
  `UnionValue.java:274-282`, `SetPredValue.java:282`), which `size`, `compareTo`, `equals`,
  `fingerPrint`, `permute` and `write` call. `FiniteSets.Cardinality` calls `size`
  (`module/FiniteSets.java:27-34`). `toSetEnum` and `deepNormalize` don't cache.
- **Who shares the object.**
  - An operator's argument is a cachable `LazyValue` (`tool/impl/SymbolNodeValueLookupProvider.java:124-146`,
    `value/impl/LazyValue.java:130-140`, `191-204`), at every call site (`Tool.java:593`, `606`,
    `1120`, `1131`). So is a LET in an expression (`Tool.java:1849-1859`). A LET in an action or
    the initial predicate binds none and evaluates again (`Tool.java:482-487`, `937-941`).
  - A partial state binds the assigned object as it is (`Tool.java:766-772`, `1365-1368`), and
    fingerprinting, which normalizes, comes once the state is complete.
  - `ValueVec.sort` compares only the elements from index 1 on as receivers
    (`value/impl/ValueVec.java:172-200`), so a set enumeration's first element, the only one of a
    singleton, is never normalized.
  - A constant definition is one object for the whole run (`tool/impl/SpecProcessor.java:237-241`).

## What the engine does

The engine rebuilds a lazy set at each use and holds variables and set elements normalized, so
where TLC shares an object it could print other counts. It declines there instead, with
"unsupported: streaming a lazy set …":

- **An operator argument or an expression's LET name** named more than once, with a use that may
  normalize it: `Compiled::is_kept` and `Compiled::kept()` (`compile/mod.rs`), whose reference is a
  `Lazy::Kept` that declines when it streams a duplicate (`compile/lazy.rs`).
- **A variable assigned a lazy set**, then streamed by `x \in` before its state is fingerprinted,
  and a name `\E` binds to the first element of a set enumeration: `Machine::held`
  (`machine.rs`) and the walker's `compile_streamed` (`compile/walker.rs`). A conjunct
  `Cardinality(v) op e` before the stream sizes v, so v streams normalized, as TLC's does.
- **A constant definition read through a variable** declines on the same path.

`prove-it-cli/tests/lazy_duplicates.rs` checks 280 specs (10 sources, 14 routes, Init and Next)
against TLC's output, at one thread and at four: each prints what TLC prints or declines.

## Still wrong on main

Each prints a "states generated" other than TLC's today, and is the next to decline or fix:

1. A held SUBSET or set of functions `\cup` a set that overlaps it:
   `Next == s' = SUBSET {1} /\ x' \in s' \cup {{1}}` generates 10 states in TLC, 7 natively.
2. A constant definition normalized elsewhere, then streamed: `C == UNION {1..2, 2..3}`,
   `Init == s = C /\ x = 0`, `Next == s' = s /\ x' \in C` generates 13 in TLC, 17 natively.
3. Stream order alone, no duplicates: through a variable, a constant via a variable or a `\E` name,
   `(SUBSET {2}) \cup {{1}}` streams `{1}` first in TLC, so a violation of `x # {1}` prints 2
   states generated in TLC and 3 natively; a LET used twice prints 3 in TLC and 2 natively.
