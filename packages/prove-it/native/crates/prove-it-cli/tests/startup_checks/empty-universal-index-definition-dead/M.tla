---- MODULE M ----
EXTENDS TLC
VARIABLE x
Init == x=0
Next == x'=x
Spec == Init /\ [][Next]_x
D == {}
P == \A i \in (IF TRUE THEN {} ELSE D) : <>(x=i)
====
