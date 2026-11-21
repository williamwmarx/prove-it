---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE s
Alias == {1, 2}
Test == PrintT(BOOLEAN \cap [i \in Alias |-> i])
Init == s = 0
Next == s' = s
Inv == Test
====
