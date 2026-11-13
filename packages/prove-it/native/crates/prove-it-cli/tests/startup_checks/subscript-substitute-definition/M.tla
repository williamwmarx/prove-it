---- MODULE M ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == TRUE
Spec == x = 0 /\ [][x' = x]_<<x, C>>
====
