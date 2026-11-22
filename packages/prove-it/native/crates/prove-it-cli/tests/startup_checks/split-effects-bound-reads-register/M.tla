---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
ASSUME TLCSet(1, {0, 1})
Init == x = 0
Next == \E v \in (TLCGet(1)) : x' = v
====
