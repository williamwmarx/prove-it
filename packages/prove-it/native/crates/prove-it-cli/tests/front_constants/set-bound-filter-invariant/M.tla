---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE s
Init == s = 0
Next == UNCHANGED s
Inv == Cardinality({x \in 1..1000001 : TRUE}) = 1000001
====
