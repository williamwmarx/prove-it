---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == (CHOOSE x \in ({1} \cup SUBSET {1}) : TRUE) = 1
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
