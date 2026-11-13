---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
P == Int \X {}
Test == PrintT(<<Cardinality(P), P>>)
ASSUME Test
====
