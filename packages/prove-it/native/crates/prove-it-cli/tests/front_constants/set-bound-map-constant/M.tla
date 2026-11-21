---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Test == Cardinality({0 : x \in 1..1000001})
ASSUME Test = 1
====
