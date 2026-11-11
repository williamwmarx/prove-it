---- MODULE AssertEqIncomparable ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == AssertEq(x, "a")
====
