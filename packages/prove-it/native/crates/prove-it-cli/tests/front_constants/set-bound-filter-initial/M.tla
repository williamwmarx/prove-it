---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE s
Init == s = Cardinality({x \in 1..1000001 : TRUE})
Next == UNCHANGED s
====
