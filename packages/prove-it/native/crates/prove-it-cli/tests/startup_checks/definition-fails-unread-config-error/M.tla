---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Test == PrintT({} \cap 0)
Bad == PrintT(1) /\ FALSE
Init == x = 0
Next == x' = x
====
