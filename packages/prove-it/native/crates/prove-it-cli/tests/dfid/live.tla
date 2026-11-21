---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x' = IF x < 2 THEN x + 1 ELSE x
Spec == Init /\ [][Next]_x
Prop == <>(x = 2)
====
