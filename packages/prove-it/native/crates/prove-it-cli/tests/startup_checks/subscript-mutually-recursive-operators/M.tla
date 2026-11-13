---- MODULE M ----
EXTENDS Naturals
VARIABLE x
RECURSIVE F(_), G(_)
F(n) == G(n)
G(n) == F(n)
Spec == x = 0 /\ [][x' = x]_<<x, F(0)>>
====
