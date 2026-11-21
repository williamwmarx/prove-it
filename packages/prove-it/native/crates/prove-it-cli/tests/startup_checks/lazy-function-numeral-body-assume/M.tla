---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == 2 = [x \in Nat |-> 2]
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
