---- MODULE Live100 ----
EXTENDS Naturals, TLC, Live100B

Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
I == INSTANCE Live100B WITH N <- 2
P == I!Q
====
