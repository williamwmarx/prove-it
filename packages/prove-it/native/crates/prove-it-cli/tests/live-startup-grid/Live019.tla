---- MODULE Live019 ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
P == \A a \in {} : \A b \in {1} : <>(x = a)
====
