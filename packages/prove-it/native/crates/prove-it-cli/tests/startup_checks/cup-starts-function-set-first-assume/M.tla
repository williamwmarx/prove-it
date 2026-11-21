---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == PrintT([a : ([STRING -> {{}, {1}}] \cup ([{1} -> {2}] \cup Nat))])
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
