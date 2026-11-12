---- MODULE M ----
EXTENDS TLC
VARIABLE x
LOCAL INSTANCE TransitiveClosure
ASSUME PrintT(Warshall({<<1, 2>>, <<2, 3>>}))
Init == x = 0
Next == x' = x
====
