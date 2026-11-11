---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets
VARIABLE x, y
Init == x = 0 /\ y = 0
F(S) == /\ x' = 1
        /\ y' = y
        /\ Cardinality(S) = 3
        /\ TRUE = [FALSE]_("a" \in S)
Next == F({x, 10, 20})
====
