---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == \E i \in {0,1} : ((x' = x) \cdot (x' = x))
====
