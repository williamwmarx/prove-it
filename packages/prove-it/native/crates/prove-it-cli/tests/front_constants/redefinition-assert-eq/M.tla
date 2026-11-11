---- MODULE M ----
EXTENDS Naturals, TLC, TLCExt
VARIABLE x
C == TRUE
D == AssertEq(1, 2)
Init == x = 0 /\ C = FALSE
Next == x' = x
====
