---- MODULE M ----
EXTENDS Naturals, FiniteSets
VARIABLE x
Init == x = 0
F(S) == Cardinality(S) = 3 /\ "a" \in S
Next == x' = x + 1
Inv == ENABLED (x' = x + 1 /\ F({x, 10, 20})')
====
