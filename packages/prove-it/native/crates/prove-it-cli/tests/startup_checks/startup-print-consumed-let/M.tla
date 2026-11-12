---- MODULE M ----
EXTENDS Integers, FiniteSets, TLC
Test == PrintT(LET P == {} \X Int IN <<Cardinality(P), <<1>> \in P>>)
ASSUME Test
====
