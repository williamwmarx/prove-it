---- MODULE M ----
EXTENDS TransitiveClosure, TLC
ASSUME Warshall({<<1,2>>,<<2,3>>}) = {<<1,2>>,<<1,3>>,<<2,3>>}
====
