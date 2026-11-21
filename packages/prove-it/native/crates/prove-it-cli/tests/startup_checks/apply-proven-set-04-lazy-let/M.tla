---- MODULE M ----
EXTENDS Naturals, FiniteSets, TLC
VARIABLE x
ASSUME LET F == 1..2 IN F[PrintT(99)]
Init == x = 0
Next == x' = x
====
