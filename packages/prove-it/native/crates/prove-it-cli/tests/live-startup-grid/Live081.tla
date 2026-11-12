---- MODULE Live081 ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
IA == INSTANCE LiveHop WITH J <- 3
P == IA!IB4!Q
====
