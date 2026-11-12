---- MODULE Live067 ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Three == 3
I == INSTANCE LiveInstanced WITH K <- Three
P == I!Q
====
