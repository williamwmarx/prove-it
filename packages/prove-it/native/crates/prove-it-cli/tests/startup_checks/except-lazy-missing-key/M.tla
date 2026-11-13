---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
ASSUME PrintT([[n \in Nat |-> n] EXCEPT ![-1] = 0][1])
Init == x = 0
Next == x' = x
====
