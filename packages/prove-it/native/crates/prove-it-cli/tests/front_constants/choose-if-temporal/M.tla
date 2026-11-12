---- MODULE M ----
VARIABLE x
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
P == IF CHOOSE n \in {} : TRUE THEN <>(x = 1) ELSE []<>(x = 0)
====
