---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLES x, y
C == 1 \div 0
Spec == x = 0 /\ y = 0 /\ [][x' = x /\ y' = y]_<<x, y, C>>
====
