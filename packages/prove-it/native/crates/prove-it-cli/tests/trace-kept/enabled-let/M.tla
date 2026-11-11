---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Inv == \A k \in {2} : LET S == {k, 1} IN Cardinality(S) = 2 /\ ENABLED (x' = 1 /\ "a" \in S)
====
