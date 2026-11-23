---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x
Spec == Init /\ [][Next]_x
RECURSIVE F(_)
F(n) == TRUE /\ <>(x = 0) /\ F(n + 1)
Prop == F(0)
====
