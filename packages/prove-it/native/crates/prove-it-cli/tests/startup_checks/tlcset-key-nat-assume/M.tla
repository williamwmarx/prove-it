---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
Test == TLCSet(Nat, 1)
ASSUME PrintT(1)
ASSUME Test
====
