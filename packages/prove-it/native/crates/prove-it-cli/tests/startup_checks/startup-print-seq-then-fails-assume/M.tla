---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
Test == LET S == {3, 1, 2} IN PrintT(Seq(S)) /\ "a" \in S
ASSUME Test
====
