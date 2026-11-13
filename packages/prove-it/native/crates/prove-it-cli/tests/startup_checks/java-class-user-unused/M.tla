---- MODULE M ----
EXTENDS TransitiveClosure, TLC
VARIABLE x
ASSUME PrintT(1)
Init == x = 0
Next == x' = x
====
