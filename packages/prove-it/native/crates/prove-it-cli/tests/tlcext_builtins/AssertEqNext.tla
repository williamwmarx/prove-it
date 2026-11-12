---- MODULE AssertEqNext ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1 /\ AssertEq(x, 1)
====
