---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
ASSUME PrintT(Int :> PrintT(2))
Init == x = 0
Next == UNCHANGED x
====
