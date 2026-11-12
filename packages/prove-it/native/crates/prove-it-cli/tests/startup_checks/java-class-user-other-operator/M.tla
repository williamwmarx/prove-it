---- MODULE M ----
EXTENDS TransitiveClosure, TLC
VARIABLE x
ASSUME PrintT(Reach)
Init == x = 0
Next == x' = x
====
