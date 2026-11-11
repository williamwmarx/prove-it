---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
CONSTANT C
VARIABLE x

Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
====
