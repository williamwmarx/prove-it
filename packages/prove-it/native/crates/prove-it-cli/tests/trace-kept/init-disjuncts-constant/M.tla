---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets
VARIABLE x
I(S) == \/ (x = 1 /\ Cardinality(S) = 2)
        \/ (x = 2 /\ "a" \in S)
Init == I({2, 1})
Next == x' = x
====
