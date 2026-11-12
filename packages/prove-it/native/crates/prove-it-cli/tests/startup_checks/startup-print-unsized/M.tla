---- MODULE M ----
EXTENDS Integers, TLC
Test == PrintT(Int \X {})
ASSUME Test
====
