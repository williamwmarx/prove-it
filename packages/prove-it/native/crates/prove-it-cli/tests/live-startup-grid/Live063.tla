---- MODULE Live063 ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
P == \A s \in {{}} : \A t \in s : <>(x = 1)
====
