---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
I == INSTANCE TransitiveClosure
Warshall(a) == a
ASSUME PrintT(Warshall(0))
Init == x = 0
Next == x' = x
====
