---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Test == PrintT(([x \in {1} |-> 1 \div 0]) \cup (Nat))
ASSUME Test
====
