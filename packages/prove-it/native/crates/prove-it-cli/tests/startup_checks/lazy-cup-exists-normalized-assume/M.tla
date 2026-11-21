---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == \E x \in ({1} \cup SUBSET {1}) : x = {}
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
