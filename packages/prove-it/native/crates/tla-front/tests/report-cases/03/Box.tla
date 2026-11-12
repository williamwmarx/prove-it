---- MODULE Box ----
VARIABLE x
Spec == x = 0 /\ [][x' = x] /\ [x, x] = 1
====
