---- MODULE S ----
EXTENDS Naturals, TLC
VARIABLE x
C == RandomElement(1..100) > 0
Init == x = RandomElement(1..100)
Next == UNCHANGED x
Spec == C /\ Init /\ [][Next]_x
Inv == x = 42
====