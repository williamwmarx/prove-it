---- MODULE M ----
EXTENDS TLC
R == [a |-> 1]
ASSUME PrintT("before") /\ ([R EXCEPT !.z = PrintT("rhs")] = R) /\ PrintT("after")
====
