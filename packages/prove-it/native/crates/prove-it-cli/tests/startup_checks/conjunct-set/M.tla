---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 1
Next == UNCHANGED x
C == Print("c", {2, 1})
Spec == C /\ Init /\ [][Next]_x
====
