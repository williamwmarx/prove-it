---- MODULE Live104 ----
EXTENDS Naturals, TLC, Live104B
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
H(a) == a
I == INSTANCE Live104B
P == I!Q
====
