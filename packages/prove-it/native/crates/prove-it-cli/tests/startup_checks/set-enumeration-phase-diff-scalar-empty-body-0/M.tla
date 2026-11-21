---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Test == PrintT((1) \ ([x \in {} |-> 1 \div 0]))
ASSUME Test
====
