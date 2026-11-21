---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT(Append(Seq({1}), {1,"a"}))
ASSUME Test
====
