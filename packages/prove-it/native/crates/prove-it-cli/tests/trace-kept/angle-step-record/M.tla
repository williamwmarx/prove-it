---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLE x, y
Init == x = 0 /\ y = 0
F(r) == /\ Cardinality(r.s) = 3
        /\ <<x' = 1 - x /\ y' = y>>_r
        /\ "a" \in r.s
Next == F([s |-> {x, 10, 20}])
====
