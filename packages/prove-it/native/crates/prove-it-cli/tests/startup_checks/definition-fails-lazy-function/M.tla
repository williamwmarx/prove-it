---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
D == PrintT(Head([y \in Nat |-> y]))
ASSUME D
Init == x = 0
Next == x' = x
====
