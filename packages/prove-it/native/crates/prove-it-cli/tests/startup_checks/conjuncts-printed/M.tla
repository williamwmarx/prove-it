---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 1
Next == UNCHANGED x
C == Print("c", TRUE)
D == Print("d", TRUE)
Spec == C /\ Init /\ D /\ [][Next]_x
====
