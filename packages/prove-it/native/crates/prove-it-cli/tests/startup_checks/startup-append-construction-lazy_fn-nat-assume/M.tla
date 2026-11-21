---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append([x \in Nat |-> 1 \div 0], Nat))
ASSUME Test
====
