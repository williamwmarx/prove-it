---- MODULE PickSuccessorSeen ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Seen == PickSuccessor(x' # 0)
====
