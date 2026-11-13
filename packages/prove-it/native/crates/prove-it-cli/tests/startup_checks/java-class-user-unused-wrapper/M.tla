---- MODULE M ----
EXTENDS TransitiveClosure, TLC
VARIABLE x
Unused(r) == Warshall(r)
ASSUME PrintT(1)
Init == x = 0
Next == x' = x
====
