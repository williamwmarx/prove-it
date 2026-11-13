---- MODULE M ----
EXTENDS TransitiveClosure, TLC, Naturals
VARIABLE x
U1(r) == Warshall(r)
Z(k) == LET L(r) == U1(r) IN k
ASSUME PrintT(Z(1) = 1)
Init == x = 0
Next == x' = x
====
