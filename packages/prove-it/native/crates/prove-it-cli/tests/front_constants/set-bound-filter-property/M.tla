---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE s
Spec == s = 0 /\ [][UNCHANGED s]_s
Prop == [](Cardinality({x \in 1..1000001 : TRUE}) = 1000001)
====
