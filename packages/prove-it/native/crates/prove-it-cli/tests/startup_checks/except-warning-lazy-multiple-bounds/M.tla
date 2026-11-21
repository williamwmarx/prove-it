---- MODULE M ----
EXTENDS Integers, TLC, FiniteSets, Sequences
VARIABLE x
ASSUME LET f[k \in {1,2}, j \in {1,2}] == [[a |-> k+j] EXCEPT !.b=0] IN f[1,1] = [a |-> 2]
Init == x = 0
Next == UNCHANGED x
====
