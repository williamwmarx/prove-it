---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
ASSUME PrintT(<<[<<1>> EXCEPT ![2] = 3], [n \in Nat |-> n]>>)
Init == x = 0
Next == UNCHANGED x
====
