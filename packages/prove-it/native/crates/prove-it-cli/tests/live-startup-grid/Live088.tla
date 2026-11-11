---- MODULE Live088 ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
I == INSTANCE Live088B WITH N <- 3
P == I!Q
====
