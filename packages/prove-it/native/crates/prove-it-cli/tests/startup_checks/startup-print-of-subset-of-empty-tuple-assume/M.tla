---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == PrintT(SUBSET <<>>)
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
