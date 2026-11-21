---- MODULE M ----
EXTENDS TransitiveClosure, TLC
ASSUME Warshall({<<1,2>>,<<3>>}) = {}
====
