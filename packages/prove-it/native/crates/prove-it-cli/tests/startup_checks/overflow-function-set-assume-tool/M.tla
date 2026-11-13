---- MODULE M ----
EXTENDS Integers, FiniteSets
VARIABLE x
ASSUME Cardinality([1..31 -> 1..2]) = 0
Init == x = 0
Next == x' = x
====
