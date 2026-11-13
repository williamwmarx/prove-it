---- MODULE M ----
EXTENDS Naturals, Sequences
VARIABLES x, y
v == <<x, y>>
I == INSTANCE Inner
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_(I!vars)
====
