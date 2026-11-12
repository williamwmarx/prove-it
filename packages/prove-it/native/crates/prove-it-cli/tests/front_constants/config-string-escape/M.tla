---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
CONSTANT C
VARIABLE x

Init == x = C
Next == UNCHANGED x
Spec == Init /\ [][Next]_x
====
