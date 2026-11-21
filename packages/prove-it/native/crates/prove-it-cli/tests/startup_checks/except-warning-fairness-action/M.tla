---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
Spec == Init /\ [][Next]_x /\ WF_x(x < 3 /\ x' = [<<x>> EXCEPT ![2] = 1][1] + 1)
P == <>(x = 3)
====
