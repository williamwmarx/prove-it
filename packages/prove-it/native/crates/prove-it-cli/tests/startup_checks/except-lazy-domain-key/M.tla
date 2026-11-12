---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
ASSUME PrintT([[n \in Nat |-> n] EXCEPT ![2] = 0][2])
Init == x = 0
Next == x' = x
====
