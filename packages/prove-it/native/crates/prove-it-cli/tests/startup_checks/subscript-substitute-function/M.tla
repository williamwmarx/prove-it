---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLES x, y, v
CONSTANT C
f[i \in {0}] == i
Spec == x = 0 /\ y = 0 /\ v = 0 /\ [][x' = x /\ y' = y /\ v' = v]_(<<x, y, v, C>>)
====
