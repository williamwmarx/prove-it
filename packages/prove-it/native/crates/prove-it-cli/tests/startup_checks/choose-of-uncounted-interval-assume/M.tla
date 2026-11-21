---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
Test == CHOOSE x \in 0..2147483647 : x = 0
VARIABLE cs
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
