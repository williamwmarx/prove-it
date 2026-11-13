---- MODULE M ----
EXTENDS Naturals
VARIABLES x, y
F(a) == <<a>>
G(a) == <<a, y>>
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_(F(x))
====
