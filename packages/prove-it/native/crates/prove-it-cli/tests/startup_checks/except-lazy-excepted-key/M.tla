---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
ASSUME PrintT([[[n \in Nat |-> n] EXCEPT ![2] = 5] EXCEPT ![2] = @ + 1][2])
Init == x = 0
Next == x' = x
====
