---- MODULE Live068 ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
I(k) == INSTANCE LiveInstanced WITH K <- k
P == I(3)!Q
====
