---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 1
Next == UNCHANGED x
C == RandomElement({TRUE})
Spec == C /\ Init /\ [][Next]_x
====
