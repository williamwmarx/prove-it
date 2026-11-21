---- MODULE M ----
EXTENDS TransitiveClosure, TLC
ASSUME Warshall({<<1,"a">>,<<"a",2>>}) = {}
====
