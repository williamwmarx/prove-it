---- MODULE M ----
EXTENDS Naturals
VARIABLE x
f[n \in Nat] == IF n = 0 THEN 0 ELSE f[n - 1]
Spec == x = 0 /\ [][x' = x]_<<x, f[3]>>
====
