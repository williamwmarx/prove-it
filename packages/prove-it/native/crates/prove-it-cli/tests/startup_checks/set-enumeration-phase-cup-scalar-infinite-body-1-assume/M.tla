---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Test == PrintT(([x \in Nat |-> 1 \div 0]) \cup (1))
ASSUME Test
====
