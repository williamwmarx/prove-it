---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
S == {Print("e", 1), 70}
Init == x = 0 /\ Cardinality(S) = 2
Next == x < 3 /\ x' = x + Cardinality(S) - 1
Inv == \A i \in 1..2 : Cardinality(S) = 2
====
