---- MODULE M ----
EXTENDS TLC
ASSUME PrintT("before") /\ ([ [a |-> [b |-> 1]] EXCEPT !.a.z = PrintT("rhs")] = [a |-> [b |-> 1]]) /\ PrintT("after")
====
