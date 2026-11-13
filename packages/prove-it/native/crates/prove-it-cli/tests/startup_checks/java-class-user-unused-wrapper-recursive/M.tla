---- MODULE M ----
EXTENDS TransitiveClosure, TLC, Naturals
VARIABLE x
RECURSIVE U1(_)
U1(r) == IF r = {} THEN Warshall(r) ELSE U1({})
ASSUME PrintT(TRUE)
Init == x = 0
Next == x' = x
====
