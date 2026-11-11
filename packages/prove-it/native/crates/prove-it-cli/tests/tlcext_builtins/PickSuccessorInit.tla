---- MODULE PickSuccessorInit ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0 /\ PickSuccessor(TRUE)
Next == x' = (x + 1) % 3
====
