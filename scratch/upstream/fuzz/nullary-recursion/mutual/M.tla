---- MODULE M ----
VARIABLE x
RECURSIVE F, G
F == G
G == F
Spec == x = 0 /\ [][x' = x]_<<x, F>>
====
