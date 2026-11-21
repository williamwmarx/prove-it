---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
Test == PrintT(([x \in {1,2} |-> x]) \ ([x \in Nat |-> x]))
ASSUME Test
====
