---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Test == PrintT((Nat) \ ([x \in Nat |-> 1 \div 0]))
ASSUME Test
====
