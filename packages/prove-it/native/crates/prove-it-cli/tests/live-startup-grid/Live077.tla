---- MODULE Live077 ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
I == INSTANCE LiveInstanced WITH K <- LET z == 3 IN z
P == I!Q
====
