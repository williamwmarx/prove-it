---- MODULE AssertErrorEnumerated ----
\* AssertError compares the failure of a membership in an enumerated set, which TLC tests by
\* asking each element whether it equals the value, as TLC words it.
EXTENDS Naturals, Sequences, TLCExt
VARIABLE x
ASSUME AssertError(
           "Attempted to compare overridden value Nat with non-overridden value:\n{}",
           {} \in {Nat})
ASSUME AssertError(
           "Attempted to compare overridden value Seq({1}) with non-overridden value:\n{}",
           {} \in {Seq({1}), 2})
ASSUME AssertError(
           "Attempted to check equality of integer 2 with non-integer:\n{}",
           {} \in {2, 1})
Init == x = 0
Next == UNCHANGED x
====
