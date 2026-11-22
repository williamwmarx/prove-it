---- MODULE M ----
EXTENDS Integers, TLC
CONSTANT C
VARIABLE x
Init == x = 0
Spec == C /\ Init /\ [][x' = 1 - x]_x
ASSUME PrintT(TLCGet("spec").inits)
====
