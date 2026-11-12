---- MODULE Live103 ----
EXTENDS Naturals, TLC, Live103C
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
I == INSTANCE Live103B
P == I!Q
====
