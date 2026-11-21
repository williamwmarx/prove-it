---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Test == PrintT((Nat) :> (Nat))
ASSUME Test
Init == x = 0
Next == UNCHANGED x
====
