---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
S == LET p == Print("e", 1) IN {p, 70}
Test == Cardinality(S) = 2 /\ Cardinality(S) = 2
ASSUME Test
Init == x = 0
Next == x' = x
====
