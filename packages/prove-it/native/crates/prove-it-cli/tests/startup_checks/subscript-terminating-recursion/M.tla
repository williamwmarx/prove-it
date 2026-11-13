---- MODULE M ----
EXTENDS Naturals
VARIABLE x
RECURSIVE F(_)
F(n) == IF n = 0 THEN 0 ELSE F(n - 1)
Spec == x = 0 /\ [][x' = x]_<<x, F(3)>>
====
