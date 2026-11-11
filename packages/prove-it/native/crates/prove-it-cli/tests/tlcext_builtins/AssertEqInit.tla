---- MODULE AssertEqInit ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x \in {0, 1} /\ AssertEq(x, 1)
Next == x < 2 /\ x' = x + 1
====
