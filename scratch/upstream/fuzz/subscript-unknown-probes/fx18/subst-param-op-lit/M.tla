---- MODULE M ----
EXTENDS Naturals
VARIABLES x, y
F(a) == <<a, y>>
G(a) == 1
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_(<<x, y, F(x)>>)
====
