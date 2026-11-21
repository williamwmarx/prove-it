---- MODULE M ----
VARIABLE v, v
Init == v=0
Next == UNCHANGED v
Spec == Init /\ [][Next]_v
====
