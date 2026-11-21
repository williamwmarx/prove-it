---- MODULE M ----
EXTENDS Naturals, FiniteSets, TLC
VARIABLE x
ASSUME LET S == {v \in {1,2}: v=1} IN /\ Cardinality(S) >= 0 /\ S[PrintT(99)]
Init == x = 0
Next == x' = x
====
