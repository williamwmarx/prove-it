---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets
VARIABLE x
Init == x = 0
Next == x' = 1 - x
F(S) == /\ Cardinality(S) = 2
        /\ ENABLED (x' = 1 /\ "a" \in S)
Inv == \A k \in {2} : F({k, 1})
====
