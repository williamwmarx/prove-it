---- MODULE Live071 ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
I == INSTANCE LiveInstanced WITH K <- 3
P == I!W
====
