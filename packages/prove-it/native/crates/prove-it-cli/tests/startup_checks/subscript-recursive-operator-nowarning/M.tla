---- MODULE M ----
EXTENDS Naturals
VARIABLE x
RECURSIVE F(_)
F(n) == F(n)
Spec == x = 0 /\ [][x' = x]_<<x, F(0)>>
====
