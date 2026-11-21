---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
T == LET g == [i \in 1..2 |-> i] IN DOMAIN [g EXCEPT ![1] = 0]
Init == x = 0
Next == UNCHANGED x
====
