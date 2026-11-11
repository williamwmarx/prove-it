---- MODULE AssertEqLazy ----
EXTENDS Naturals, TLCExt
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == AssertEq(SUBSET {x, 7}, {}) \/ AssertEq([i \in {x} |-> i], [i \in {0} |-> 1]) \/ AssertEq([{x} -> {1, 2}], {}) \/ TRUE
====
