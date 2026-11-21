---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE x
Test == PrintT((STRING) :> (Int))
ASSUME Test
Init == x = 0
Next == UNCHANGED x
====
