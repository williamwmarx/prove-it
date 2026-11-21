---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(Nat, {1,"a"}))
ASSUME Test
====
