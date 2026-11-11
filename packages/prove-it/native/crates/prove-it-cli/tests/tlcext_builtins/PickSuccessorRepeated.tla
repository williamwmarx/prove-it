---- MODULE PickSuccessorRepeated ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
Next == x < 4 /\ (x' = x + 1 \/ (x >= 1 /\ x' = 2) \/ x' = x + 1)
Pick == PickSuccessor(x' # 2 \/ x = 1)
Inv == x < 4
====
