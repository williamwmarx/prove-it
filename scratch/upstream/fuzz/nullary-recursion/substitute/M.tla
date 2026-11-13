---- MODULE M ----
VARIABLE x
CONSTANT C
RECURSIVE D
D == D
Spec == x = 0 /\ [][x' = x]_<<x, C>>
====
