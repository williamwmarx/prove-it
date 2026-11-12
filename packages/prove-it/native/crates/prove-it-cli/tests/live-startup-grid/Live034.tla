---- MODULE Live034 ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
P == []<>(x = 1)
Q == \A c \in {} : []FALSE
====
