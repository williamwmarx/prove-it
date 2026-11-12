---- MODULE Live086 ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
I == INSTANCE LiveInstanced WITH K <- {0, 1}
P == I!R
====
