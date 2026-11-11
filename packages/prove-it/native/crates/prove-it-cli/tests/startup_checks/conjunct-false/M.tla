---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 1
Next == UNCHANGED x
C == Print("c", FALSE)
Spec == C /\ Init /\ [][Next]_x
====
