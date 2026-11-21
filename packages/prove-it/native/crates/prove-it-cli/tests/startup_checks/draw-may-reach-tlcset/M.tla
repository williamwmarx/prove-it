---- MODULE M ----
EXTENDS Integers, TLC
Test == (RandomElement({1, 2}) = 2) /\ TLCSet(1, 2)
ASSUME Test \/ TRUE
====
