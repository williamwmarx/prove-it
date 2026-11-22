---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Spec == LET N == [][x' = 1 - x]_x IN Init /\ N
ASSUME PrintT(TLCGet("spec"))
====
