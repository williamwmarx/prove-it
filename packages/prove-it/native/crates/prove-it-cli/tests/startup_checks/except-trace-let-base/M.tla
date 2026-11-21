---- MODULE M ----
EXTENDS TLC
ASSUME LET R == [a |-> 1] IN PrintT("before") /\ ([R EXCEPT !.z = PrintT("rhs")] = R) /\ PrintT("after")
====
