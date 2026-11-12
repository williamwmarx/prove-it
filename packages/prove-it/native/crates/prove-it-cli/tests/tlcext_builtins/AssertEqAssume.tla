---- MODULE AssertEqAssume ----
EXTENDS Naturals, TLCExt
VARIABLE x
ASSUME AssertEq(1, 2) \/ TRUE
Init == x = 0
Next == x < 2 /\ x' = x + 1
====
