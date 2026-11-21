---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Test == PrintT((Nat) \ ([x \in {1} |-> 1 \div 0]))
ASSUME Test
====
