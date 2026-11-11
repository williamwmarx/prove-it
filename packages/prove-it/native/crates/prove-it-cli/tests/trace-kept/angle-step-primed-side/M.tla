---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLE x, y
Init == x = 0 /\ y = 0
F(S) == /\ Cardinality(S) = 3
        /\ <<x' = 1 - x /\ y' = y>>_S
        /\ "a" \in S
Next == F({x, 10, 20})
====
