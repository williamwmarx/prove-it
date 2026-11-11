---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == x' = 1 - x /\ y' = y
G(S) == ENABLED (Cardinality(S) = 3 /\ y' = y /\ UNCHANGED Len(<<S>>) /\ x' = 1 - x /\ "a" \in S)
Inv == G({y, 10, 20})
====
