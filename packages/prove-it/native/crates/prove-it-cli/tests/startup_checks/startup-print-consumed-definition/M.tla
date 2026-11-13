---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
P == Int \X {}
Test == PrintT(<<P = {}, Cardinality(P) + 1>>)
ASSUME Test
====
