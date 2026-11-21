---- MODULE M ----
EXTENDS TLCExt, TLC
VARIABLE x
ASSUME AssertEq(1, 1) /\ TLCGetOrDefault(3, 5) = 5
Init == x = 0
Next == x' = x
====
