---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
F(a) == {a} \cup {y \in {5} : Print("f", TRUE)}
S == {F(1)}
Inv == Cardinality(S) = 1 /\ Cardinality(S) = 1
Init == x = 0
Next == x' = x
====
