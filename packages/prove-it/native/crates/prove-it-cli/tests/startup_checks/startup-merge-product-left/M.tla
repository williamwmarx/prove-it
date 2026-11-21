---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
Test == PrintT(({1,2} \X {3}) @@ Nat)
ASSUME Test
====
