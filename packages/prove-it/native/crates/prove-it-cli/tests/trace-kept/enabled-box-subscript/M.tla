---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets
VARIABLE x
Init == x = 0
Next == x' = 1 - x
F(S) == Cardinality(S) = 3 /\ [FALSE]_("a" \in S)
Inv == ENABLED (x' = 1 /\ F({x, 10, 20}))
====
