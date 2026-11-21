---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE s
Test == PrintT(BOOLEAN \cap [<<i,j>> \in {<<1,2>>} |-> i + j])
Init == s = 0 /\ Test
Next == s' = s
Inv == Test
====
