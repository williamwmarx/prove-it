---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == LET S == [i \in 1..2 |-> i] IN PrintT(Append(S, 3))
ASSUME Test
====
