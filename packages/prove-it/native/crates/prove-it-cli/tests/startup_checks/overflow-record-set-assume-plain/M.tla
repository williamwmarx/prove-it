---- MODULE M ----
EXTENDS Integers, FiniteSets
VARIABLE x
ASSUME Cardinality([a : 1..65536, b : 1..65536]) = 0
Init == x = 0
Next == x' = x
====
