---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
CONSTANT C
VARIABLE x
D == {3, 1}
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
====
