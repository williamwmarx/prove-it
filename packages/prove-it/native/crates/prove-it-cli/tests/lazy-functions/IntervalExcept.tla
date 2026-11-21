---- MODULE IntervalExcept ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == UNCHANGED x
ASSUME PrintT([[n \in 1..2 |-> n] EXCEPT ![1] = 5])
ASSUME [[n \in 1..2 |-> n] EXCEPT ![FALSE] = 0] = 0
====
