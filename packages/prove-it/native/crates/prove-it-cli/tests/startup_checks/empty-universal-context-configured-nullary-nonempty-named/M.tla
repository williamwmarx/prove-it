---- MODULE M ----
EXTENDS Naturals, B
Init == x=0
Next == x'=(x+1)%3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
I == INSTANCE B
P == I!Q
====
