---- MODULE Live102 ----
EXTENDS Naturals, TLC, Live102B

Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
I == INSTANCE Live102B WITH N <- 2
S1 == {2}
P == I!Q
====
