---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
F(a) == Print("e", a)
S == {F(1), 70}
Inv == Cardinality(S) = 2 /\ Cardinality(S) = 2
Init == x = 0
Next == x' = x
====
