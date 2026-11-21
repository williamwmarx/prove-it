---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == (UNION {{1}, SUBSET {1}}) \subseteq {1}
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
