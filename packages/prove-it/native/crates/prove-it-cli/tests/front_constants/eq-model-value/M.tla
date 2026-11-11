---- MODULE M ----
VARIABLE x
CONSTANT A
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
Prop == <>(1 = A)
====
