---- MODULE AssertEqConstant ----
EXTENDS Naturals, TLCExt
VARIABLE x
C == AssertEq(1, 2)
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == C \/ x >= 0
====
