---- MODULE AssertEqEnabled ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
A == x < 2 /\ x' = x + 1 /\ AssertEq(x', 2)
Next == A
Inv == ENABLED A \/ TRUE
====
