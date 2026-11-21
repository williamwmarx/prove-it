---- MODULE M ----
EXTENDS TransitiveClosure
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Inv == Warshall({<<1, 2>>}) = {<<1, 2>>}
====
