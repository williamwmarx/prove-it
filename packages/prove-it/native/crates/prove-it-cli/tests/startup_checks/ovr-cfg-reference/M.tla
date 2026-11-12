---- MODULE M ----
EXTENDS AnySet, TLC
CONSTANT K
VARIABLE x
ASSUME PrintT(K)
Init == x = 0
Next == x' = x
====
