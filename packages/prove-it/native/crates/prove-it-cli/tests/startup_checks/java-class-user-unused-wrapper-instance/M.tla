---- MODULE M ----
EXTENDS TLC, Naturals
I == INSTANCE TransitiveClosure
VARIABLE x
U1(r) == I!Warshall(r)
ASSUME PrintT(TRUE)
Init == x = 0
Next == x' = x
====
