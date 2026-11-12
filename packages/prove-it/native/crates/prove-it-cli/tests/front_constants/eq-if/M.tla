---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x
Prop == <>[](IF x = 1 THEN x = 2 ELSE 1 = {})
====
