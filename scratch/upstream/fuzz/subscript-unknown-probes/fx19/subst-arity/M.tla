---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLES x, y, v
CONSTANT C
G(a) == <<a, x>>
Spec == x = 0 /\ y = 0 /\ v = 0 /\ [][x' = x /\ y' = y /\ v' = v]_(<<y, v, C>>)
====
