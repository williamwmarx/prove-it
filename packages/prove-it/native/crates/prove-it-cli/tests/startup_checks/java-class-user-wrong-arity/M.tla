---- MODULE M ----
EXTENDS TransitiveClosure, TLC
VARIABLE x
ASSUME PrintT(Warshall)
Init == x = 0
Next == x' = x
====
