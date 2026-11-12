---- MODULE Live025 ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
P == <>(IF TRUE THEN 7 ELSE x = 0)
====
