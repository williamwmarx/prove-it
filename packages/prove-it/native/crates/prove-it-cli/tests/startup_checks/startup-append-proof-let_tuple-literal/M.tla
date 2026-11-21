---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(LET S == <<1>> IN S, 3))
ASSUME Test
====
