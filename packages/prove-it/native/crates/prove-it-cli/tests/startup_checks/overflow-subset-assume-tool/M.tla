---- MODULE M ----
EXTENDS Integers, FiniteSets
VARIABLE x
ASSUME Cardinality(SUBSET (1..31)) = 0
Init == x = 0
Next == x' = x
====
