---- MODULE M ----
EXTENDS TLC, Naturals
LOCAL INSTANCE TransitiveClosure
VARIABLE x
U1(r) == Warshall(r)
Inv == U1({<<1, 2>>, <<2, 3>>}) = U1({<<1, 2>>, <<2, 3>>})
ASSUME PrintT(TRUE)
Init == x = 0
Next == x' = x
====
