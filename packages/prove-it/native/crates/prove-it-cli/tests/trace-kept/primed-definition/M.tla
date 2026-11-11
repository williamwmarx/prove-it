---- MODULE M ----
EXTENDS Naturals, FiniteSets
VARIABLE x
Init == x = 0
F(S) == Cardinality(S) = 3 /\ "a" \in S
D == F({x, 10, 20})
Next == x' = x + 1 /\ D'
====
