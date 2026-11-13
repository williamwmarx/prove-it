---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLES x, y, v
I == INSTANCE Inner
Spec == x = 0 /\ y = 0 /\ v = 0 /\ [][x' = x /\ y' = y /\ v' = v]_(<<x, y, I!vars>>)
====
