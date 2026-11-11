---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets
VARIABLE x
Init == x = 0
F(S) == Cardinality(S) = 3 /\ UNCHANGED ("a" \in S)
Next == x' = 1 - x /\ ENABLED (x' = 1 /\ F({x, 10, 20}))
====
