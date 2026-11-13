---- MODULE M ----
VARIABLE x
RECURSIVE F
F == F
Spec == x = 0 /\ [][x' = x]_<<x, F>>
====
