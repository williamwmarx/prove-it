---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == (CHOOSE f \in [{1, 2} -> {2}] : TRUE)[FALSE] = 1
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
