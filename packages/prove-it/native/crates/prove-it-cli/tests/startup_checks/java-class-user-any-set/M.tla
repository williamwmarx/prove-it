---- MODULE M ----
EXTENDS AnySet, TLC
VARIABLE x
ASSUME PrintT(ANY)
Init == x = 0
Next == x' = x
====
