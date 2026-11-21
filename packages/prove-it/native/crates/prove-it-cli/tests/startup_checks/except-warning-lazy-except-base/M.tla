---- MODULE M ----
EXTENDS Integers, TLC, FiniteSets, Sequences
VARIABLE x
ASSUME LET f[k \in {1,2}] == [[a |-> k] EXCEPT !.b = 0] IN [f EXCEPT ![1] = [a |-> 9]][1] = [a |-> 9]
Init == x = 0
Next == UNCHANGED x
====
