---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets
VARIABLE x
Init == x = 0
Next == x' = 1 - x
ASSUME LET S == {2, 1} IN Cardinality(S) = 2 /\ "a" \in S
====
