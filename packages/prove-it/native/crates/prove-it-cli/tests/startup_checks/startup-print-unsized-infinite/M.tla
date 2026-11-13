---- MODULE M ----
EXTENDS Integers, Sequences, TLC
Test == PrintT({1} \X Seq({1}))
ASSUME Test
====
