---- MODULE Live105 ----
EXTENDS Naturals, TLC, Live105B
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
I == INSTANCE Live105B
P == I!Q
====
