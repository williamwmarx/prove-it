---- MODULE M ----
EXTENDS Naturals, FiniteSets, TLC
Size(S) == Cardinality(S \X {0})
Test == PrintT(Size({1, 2}))
ASSUME Test
====
