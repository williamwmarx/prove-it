---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
C == Print("c", TRUE)
Init == x = 1
Next == UNCHANGED x
Spec == C /\ Init /\ [][Next]_x
====
