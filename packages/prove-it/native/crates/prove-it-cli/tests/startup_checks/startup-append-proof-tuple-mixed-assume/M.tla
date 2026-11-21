---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(<<>>, {1,"a"}))
ASSUME Test
====
