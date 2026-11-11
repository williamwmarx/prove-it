---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets
VARIABLE x
Init == x = 0
F(S) == Cardinality(S) = 2 /\ ENABLED (x' = 1 /\ "a" \in S)
Next == \E k \in {2} : x' = 1 - x /\ F({k, 1})
====
