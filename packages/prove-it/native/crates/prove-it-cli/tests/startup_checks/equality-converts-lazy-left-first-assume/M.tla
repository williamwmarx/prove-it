---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE cs
Test == (<<1, 2>> \ {3}) = {b \in [a : {"a", 1}] : TRUE}
ASSUME Test
Init == cs = 0
Next == cs' = cs
====
