---- MODULE M ----
EXTENDS Naturals, FiniteSets
VARIABLE x, y
Init == x = 1 /\ y = 0
F(S) == IF Cardinality(S) = 3 THEN "a" \in S ELSE TRUE
Next == x' = x + 1 /\ y' = y /\ UNCHANGED F({x, 1, 2})
====
