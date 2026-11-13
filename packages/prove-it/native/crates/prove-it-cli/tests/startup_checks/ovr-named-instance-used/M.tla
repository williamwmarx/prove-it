---- MODULE M ----
EXTENDS TLC
VARIABLE x
I == INSTANCE TransitiveClosure
ASSUME PrintT(I!Warshall({<<1, 2>>, <<2, 3>>}))
Init == x = 0
Next == x' = x
====
