---- MODULE Live029 ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
P == []<>(x = 0) \/ \A c \in {} : []FALSE
====
