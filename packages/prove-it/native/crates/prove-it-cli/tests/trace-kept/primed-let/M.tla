---- MODULE M ----
EXTENDS Naturals, FiniteSets
VARIABLE x
Init == x = 0
Next == x' = x + 1 /\ (LET S == {x, 10, 20} IN Cardinality(S) = 3 /\ "a" \in S)'
====
