---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0 /\ [i \in {1, 2} |-> PrintT(i)][3] = 1
Next == UNCHANGED x
====
