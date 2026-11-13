---- MODULE M ----
EXTENDS Naturals, Sequences
VARIABLES x, y
Z == <<x, y>>
C2 == Len(<<1>>)
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_(<<x, y, C2>>)
====
