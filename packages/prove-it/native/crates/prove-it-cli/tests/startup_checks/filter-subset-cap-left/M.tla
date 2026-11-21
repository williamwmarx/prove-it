---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE state
ASSUME PrintT(({v \in SUBSET {1} : FALSE} \cap {1}) = {})
Init == state = 0
Next == UNCHANGED state
====
