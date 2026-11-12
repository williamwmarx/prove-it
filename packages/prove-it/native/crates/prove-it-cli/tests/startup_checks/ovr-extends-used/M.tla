---- MODULE M ----
EXTENDS TransitiveClosure, TLC
VARIABLE x

ASSUME PrintT(Warshall({<<1, 2>>, <<2, 3>>}))
Init == x = 0
Next == x' = x
====
