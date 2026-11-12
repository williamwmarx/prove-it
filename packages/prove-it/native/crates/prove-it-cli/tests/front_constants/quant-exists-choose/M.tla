---- MODULE M ----
VARIABLE x
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
P == \E k \in {CHOOSE n \in {} : TRUE} : <>(x = k)
====
