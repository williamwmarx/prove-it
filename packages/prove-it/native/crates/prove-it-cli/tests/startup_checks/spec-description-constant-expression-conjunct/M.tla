---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Spec == (1 = 1) /\ Init /\ [][x' = 1 - x]_x
ASSUME PrintT(TLCGet("spec").inits)
====
