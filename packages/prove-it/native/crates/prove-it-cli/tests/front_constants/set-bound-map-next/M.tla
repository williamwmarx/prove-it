---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE s
Init == s = 0
Next == s' = Cardinality({x : x \in 1..1000001})
====
