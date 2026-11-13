---- MODULE M ----
VARIABLE x
RECURSIVE F
F == <<x, F>>
Spec == x = 0 /\ [][x' = x]_<<x, F>>
====
