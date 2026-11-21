---- MODULE M ----
EXTENDS Naturals, FiniteSets, TLC
VARIABLE x
ASSUME ({})[PrintT(99)]
Init == x = 0
Next == x' = x
====
