---- MODULE M ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Spec == Init /\ [][Next]_x
P == \E k \in {1 \div 0} : <>(x = k)
====
