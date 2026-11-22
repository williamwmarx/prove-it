---- MODULE M ----
EXTENDS Integers, TLC
CONSTANT C
VARIABLE x
Init == x = 0
Spec == (1 = 1) /\ TRUE /\ Init /\ [][x' = 1 - x]_x
ASSUME PrintT(TLCGet("spec").inits)
====
