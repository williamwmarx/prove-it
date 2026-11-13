---- MODULE M ----
EXTENDS Naturals
VARIABLES x, y
CONSTANT C(_)
G(a) == <<a, y>>
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_(C(x))
====
