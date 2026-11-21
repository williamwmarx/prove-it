---- MODULE M ----
EXTENDS Integers, Sequences, TLC
VARIABLE s
Test == PrintT(BOOLEAN \cap [i \in ([{1} -> {2, 3}] \ ({1} \cup {2})) |-> i])
ASSUME Test
Init == s = 0
Next == s' = s
Inv == Test
====
