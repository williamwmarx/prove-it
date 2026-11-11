---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 1
Next == UNCHANGED x
C == Print("c", 1 \div 0 > 1)
Spec == C /\ Init /\ [][Next]_x
====
