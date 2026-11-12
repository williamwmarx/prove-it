---- MODULE M ----
VARIABLE x
Init == 1
Next == x' = x
Spec == Init /\ [][Next]_x
====
