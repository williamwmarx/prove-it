---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == Cardinality({1} \cup SUBSET {1}) = 3
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
