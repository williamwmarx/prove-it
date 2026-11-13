---- MODULE M ----
EXTENDS TLC, Naturals
LOCAL INSTANCE TransitiveClosure
VARIABLE x
U1(r) == Warshall(r)
Ap(F(_), r) == F(r)
Use == 1
ASSUME PrintT(TRUE)
Init == x = 0
Next == x' = x
====
