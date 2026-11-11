---- MODULE LazyApply ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == /\ [i \in {0,1} |-> i = x][x] /\ x' = 1-x
====
