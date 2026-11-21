---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == ({2, 3} \cup SUBSET {1}) \subseteq {7}
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
