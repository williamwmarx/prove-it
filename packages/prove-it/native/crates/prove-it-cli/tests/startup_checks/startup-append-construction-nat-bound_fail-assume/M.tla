---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(Nat, [x \in 1 \div 0 |-> x]))
ASSUME Test
====
