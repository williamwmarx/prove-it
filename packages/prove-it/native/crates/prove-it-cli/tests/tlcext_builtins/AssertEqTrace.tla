---- MODULE AssertEqTrace ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
Next == \/ x < 3 /\ AssertEq(x, 5) /\ x' = x + 2
        \/ x < 3 /\ x' = x + 1
Inv == x < 3
====
