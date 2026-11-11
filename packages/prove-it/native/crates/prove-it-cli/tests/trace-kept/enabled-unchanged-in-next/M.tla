---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLE x, y
Init == x = 0 /\ y = 0
G(S) == ENABLED (Cardinality(S) = 3 /\ x' = 1 - x /\ y' = y /\ UNCHANGED Len(<<S>>) /\ "a" \in S)
Next == x' = 1 - x /\ y' = y /\ G({y, 10, 20})
====
