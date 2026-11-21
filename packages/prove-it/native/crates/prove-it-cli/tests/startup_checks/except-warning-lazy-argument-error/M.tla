---- MODULE M ----
EXTENDS Integers, TLC, FiniteSets, Sequences
VARIABLE x
ASSUME LET f[k \in {1,2}] == [[a |-> k] EXCEPT !.b = 0] IN f[1 \div 0] = [a |-> 1]
Init == x = 0
Next == UNCHANGED x
====
