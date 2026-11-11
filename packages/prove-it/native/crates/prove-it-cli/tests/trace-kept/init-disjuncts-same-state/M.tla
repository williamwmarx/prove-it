---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets
VARIABLE x
I(S) == \/ (x = 1 /\ Cardinality(S) = 2)
        \/ (x = 1 /\ "a" \in S)
Init == \E k \in {2} : I({k, 1})
Next == x' = x
====
