---- MODULE M ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x
P == \A k \in 0..1 : <>(2 \in 1)
====
