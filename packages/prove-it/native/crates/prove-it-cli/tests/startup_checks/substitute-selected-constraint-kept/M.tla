---- MODULE M ----
EXTENDS TLC, Integers
VARIABLE x
Init == x = 0
Next == x' = x
CONSTANT J
K == FALSE
B == TRUE
ASSUME PrintT(J)
====
