---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Test == PrintT(SUBSET {1, 2})
Init == x = 0 /\ Test
Next == x < 2 /\ x' = x + 1 /\ Test
Inv == Test /\ x < 2
====
