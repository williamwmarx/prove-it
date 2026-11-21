---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
P(m, v) == IF PrintT(m) THEN v ELSE v
Init == [i \in {1, 2} |-> P(i, x = i)][2]
Next == UNCHANGED x
====
