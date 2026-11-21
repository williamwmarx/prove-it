---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE s
Test == PrintT(BOOLEAN \cap [i \in {1, 2} |-> i * 2])
ASSUME Test
Init == s = 0
Next == s' = s
Inv == Test
====
