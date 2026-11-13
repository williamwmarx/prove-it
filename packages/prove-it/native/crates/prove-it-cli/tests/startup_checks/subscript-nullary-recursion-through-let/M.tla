---- MODULE M ----
VARIABLE x
RECURSIVE F
F == LET H == F IN H
Spec == x = 0 /\ [][x' = x]_<<x, F>>
====
