---- MODULE M ----
EXTENDS Naturals, Sequences
VARIABLES x, y
W == 2
D3 == 1
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_(<<x, y, W>>)
====
