---- MODULE CardinalityTupleUnsortable ----
EXTENDS Naturals, FiniteSets, TLC
VARIABLE x
Init == x = 0
Next == x' = x
ASSUME Cardinality(<<{1, "a"}>>) = 1
====
