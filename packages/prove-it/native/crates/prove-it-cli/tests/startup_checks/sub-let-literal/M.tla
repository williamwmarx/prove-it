---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLES x, y
C == 1
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_(LET L == 1 IN L)
====
