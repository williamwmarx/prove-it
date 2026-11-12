---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLES x, y
C == <<PrintT(1), 2>>
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_<<x, y, C>>
====
