---- MODULE M ----
EXTENDS Integers, Sequences, TLC
S == [i \in 1..2 |-> i]
Test == PrintT(Append(S, 3))
ASSUME Test
====
