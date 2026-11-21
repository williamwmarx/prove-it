---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 1
S(y) == LET D == y IN Init /\ D /\ [][x' = x]_x
Spec == S(x)
====
