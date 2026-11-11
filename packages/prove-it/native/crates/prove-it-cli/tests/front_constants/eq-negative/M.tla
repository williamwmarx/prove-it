---- MODULE M ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
Prop == <>(-1 = "a")
====
