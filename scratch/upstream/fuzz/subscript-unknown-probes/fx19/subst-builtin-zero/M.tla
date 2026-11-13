---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLES x, y, v
CONSTANT C
Spec == x = 0 /\ y = 0 /\ v = 0 /\ [][x' = x /\ y' = y /\ v' = v]_(<<x, y, v, C>>)
====
