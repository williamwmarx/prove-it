---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
F(S) == /\ Cardinality(S) = 2
        /\ ENABLED (x' = 1 /\ (x = 2 => "a" \in S))
Inv == \A k \in {2} : F({k, 1})
====
