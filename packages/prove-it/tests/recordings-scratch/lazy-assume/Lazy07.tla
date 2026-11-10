---- MODULE Lazy07 ----
EXTENDS Integers
VARIABLE x
ASSUME ~("a" \in 3..1)
Init == x = 0
Next == x' = x
====
