---- MODULE M ----
EXTENDS TransitiveClosure, TLC, Naturals
VARIABLE x
U1(r) == Warshall(r)
Z(k) == LET L(r) == U1(r) IN L(k)
ASSUME PrintT(Z({<<1, 2>>, <<2, 3>>}) = Z({<<1, 2>>, <<2, 3>>}))
Init == x = 0
Next == x' = x
====
