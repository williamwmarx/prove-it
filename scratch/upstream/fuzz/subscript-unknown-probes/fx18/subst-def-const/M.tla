---- MODULE M ----
EXTENDS Naturals, Sequences
VARIABLES x, y
W == 1
D2 == <<x, y>>
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_(W)
====
