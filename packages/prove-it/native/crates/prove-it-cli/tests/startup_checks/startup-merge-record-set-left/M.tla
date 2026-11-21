---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
Test == PrintT([a: {1,2}] @@ Nat)
ASSUME Test
====
