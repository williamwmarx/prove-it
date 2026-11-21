---- MODULE M ----
EXTENDS TLC, Integers, E
VARIABLE x
Init == x = 0
Next == x' = x
CONSTANT J
ASSUME PrintT(J)
====
