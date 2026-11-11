---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == /\ x' = 1
        /\ y' = y
        /\ IF LET S == {x, 10, 20} IN Cardinality(S) = 3 /\ UNCHANGED ("a" \in S) THEN TRUE ELSE TRUE
====
