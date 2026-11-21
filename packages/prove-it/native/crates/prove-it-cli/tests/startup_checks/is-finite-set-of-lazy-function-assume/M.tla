---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == PrintT(IsFiniteSet([x \in Nat |-> x]))
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
