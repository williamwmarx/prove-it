---- MODULE M ----
EXTENDS TransitiveClosure, TLC, Naturals
VARIABLE x
U1(r) == Warshall(r)
Ap(F(_), r) == F(r)
ASSUME PrintT(Ap(U1, {<<1, 2>>, <<2, 3>>}) = Ap(U1, {<<1, 2>>, <<2, 3>>}))
Init == x = 0
Next == x' = x
====
