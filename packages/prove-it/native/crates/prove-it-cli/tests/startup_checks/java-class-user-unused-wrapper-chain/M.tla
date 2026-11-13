---- MODULE M ----
EXTENDS TransitiveClosure, TLC, Naturals
VARIABLE x
U1(r) == Warshall(r)
U2(r) == U1(r)
ASSUME PrintT(TRUE)
Init == x = 0
Next == x' = x
====
