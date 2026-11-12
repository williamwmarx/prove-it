---- MODULE PickSuccessorInvariant ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Incomplete == PickSuccessor(TRUE)
====
