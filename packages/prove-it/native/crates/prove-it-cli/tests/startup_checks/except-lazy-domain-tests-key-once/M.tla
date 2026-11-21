---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Test == PrintT([[v \in {v \in Nat : PrintT(v)} |-> v] EXCEPT ![2] = 5]) /\ [[v \in {v \in Nat : PrintT(v)} |-> v] EXCEPT ![2] = 5][3] = 3
ASSUME Test
Init == x = 0
Next == x' = x
====
