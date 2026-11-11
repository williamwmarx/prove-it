---- MODULE M ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x
P == \A j \in {1} : \A k \in 1 : <>(x = k)
====
