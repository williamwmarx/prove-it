---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE s
Test == PrintT(BOOLEAN \cap [i \in {1}, j \in {2} |-> i + j])
Init == s = 0
Next == s' = 1 /\ Test
Inv == Test
====
