---- MODULE Live069 ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
K == 4
I == INSTANCE LiveInstanced
P == I!Q
====
