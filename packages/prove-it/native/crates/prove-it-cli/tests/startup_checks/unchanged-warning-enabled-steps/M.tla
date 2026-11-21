---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
A == x' = 1 - x /\ UNCHANGED x
B == x' = 1 - x
Next == A \/ B
Spec == Init /\ [][Next]_x /\ WF_x(A)
P == <>(x = 1)
====
