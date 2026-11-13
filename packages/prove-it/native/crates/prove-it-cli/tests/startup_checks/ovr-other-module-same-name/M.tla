---- MODULE M ----
EXTENDS Other, TLC
VARIABLE x
I == INSTANCE TransitiveClosure
ASSUME PrintT(Warshall({<<1, 2>>}))
Init == x = 0
Next == x' = x
====
