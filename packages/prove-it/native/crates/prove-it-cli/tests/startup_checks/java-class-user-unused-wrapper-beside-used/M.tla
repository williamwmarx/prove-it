---- MODULE M ----
EXTENDS TransitiveClosure, TLC, Naturals
VARIABLE x
U1(r) == Warshall(r)
U2(r) == U1(r)
V(r) == r
ASSUME PrintT(V({<<1, 2>>, <<2, 3>>}) = {<<1, 2>>, <<2, 3>>})
Init == x = 0
Next == x' = x
====
