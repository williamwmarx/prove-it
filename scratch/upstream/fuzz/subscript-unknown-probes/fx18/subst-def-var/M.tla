---- MODULE M ----
EXTENDS Naturals, Sequences
VARIABLES x, y
W == 2
D4 == y
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_(<<x, W>>)
====
