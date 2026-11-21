---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(Nat, 1 \div 0))
ASSUME Test
====
