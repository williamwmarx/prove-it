---- MODULE PickSuccessorUnassigned ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
Next == PickSuccessor(TRUE) /\ x' = (x + 1) % 3
====
