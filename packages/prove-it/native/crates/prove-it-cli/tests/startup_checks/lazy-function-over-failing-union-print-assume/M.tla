---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == PrintT([b \in UNION ({1} \cup {1}) |-> Len(<<0, 7>>)])
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
