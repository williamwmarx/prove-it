---- MODULE M ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = Cardinality(SUBSET (1..31))
Next == x' = x
====
