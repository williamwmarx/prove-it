---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE state
ASSUME PrintT(({1} \cap {v \in SUBSET {1} : FALSE}) = {})
Init == state = 0
Next == UNCHANGED state
====
