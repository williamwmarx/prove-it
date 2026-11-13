---- MODULE M ----
EXTENDS Naturals
VARIABLE x
RECURSIVE F(_)
H(v) == v
F(n) == H(F(n))
Spec == x = 0 /\ [][x' = x]_<<x, F(0)>>
====
