---- MODULE M ----
EXTENDS TransitiveClosure, TLC
ASSUME PrintT({e \in Warshall({<<1,100>>,<<100,3>>,<<2,0>>}): PrintT(e)})
====
