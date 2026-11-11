---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets
VARIABLE x, y
Init == x = 0 /\ y = 0
F(S) == /\ x' = 1
        /\ Cardinality(S) = 3
        /\ y' = y
        /\ x' # x => UNCHANGED ("a" \in S)
Next == F({x, 10, 20})
Inv == TRUE
====
