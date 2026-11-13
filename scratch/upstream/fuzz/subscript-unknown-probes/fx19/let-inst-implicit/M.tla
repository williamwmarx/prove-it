---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLES x, y, v
W == 1
Spec == x = 0 /\ y = 0 /\ v = 0 /\ [][x' = x /\ y' = y /\ v' = v]_(LET I == INSTANCE Inner IN <<x, y, I!vars>>)
====
