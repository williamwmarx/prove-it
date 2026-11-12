---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
VARIABLE x
D == PrintT("d")
C == x = 0
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
====
