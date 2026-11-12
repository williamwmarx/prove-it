---- MODULE Live065 ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
I == INSTANCE LiveInstanced WITH K <- 1 + 2
P == I!Q
====
