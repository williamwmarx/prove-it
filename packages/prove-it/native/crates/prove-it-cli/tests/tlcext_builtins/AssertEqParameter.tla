---- MODULE AssertEqParameter ----
EXTENDS Naturals, TLCExt
VARIABLE x
Check(v) == AssertEq(v, 1)
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == \A i \in {x, x + 1} : Check(i) \/ TRUE
====
