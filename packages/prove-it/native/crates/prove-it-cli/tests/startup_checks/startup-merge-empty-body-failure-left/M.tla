---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
Test == PrintT([i \in {} |-> 1 \div 0] @@ Nat)
ASSUME Test
====
