---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(BOOLEAN, Nat))
ASSUME Test
====
