---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
Test == PrintT(Nat @@ [a |-> 1])
ASSUME Test
====
