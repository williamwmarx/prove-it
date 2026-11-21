---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == x' = 1 - x
A == x' = 1 - x /\ UNCHANGED x
Spec == Init /\ [][Next]_x /\ WF_x(Next)
P == []<>(ENABLED A) \/ <>(x = 1)
====
