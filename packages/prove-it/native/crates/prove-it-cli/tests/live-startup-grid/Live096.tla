---- MODULE Live096 ----
EXTENDS Naturals, TLC
G(a) == 3
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
I == INSTANCE Live096B WITH N <- 3, F <- G
P == I!QA5
====
