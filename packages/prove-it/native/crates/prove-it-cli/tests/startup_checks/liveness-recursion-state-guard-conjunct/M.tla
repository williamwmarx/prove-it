---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
RECURSIVE F(_)
F(n) == TRUE /\ IF x = 2 THEN <>(x = 1) ELSE (<>(x = 1) /\ F(n + 1))
Prop == F(0)
====
