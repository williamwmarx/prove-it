---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append([x \in {} |-> 1 \div 0], Nat))
ASSUME Test
====
