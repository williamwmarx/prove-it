---- MODULE PickSuccessorConstraint ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Con == PickSuccessor(TRUE)
====
