---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
Test == PrintT(<<1,2>> @@ Nat)
ASSUME Test
====
