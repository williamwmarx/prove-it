---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
RECURSIVE F(_)
F(n) == IF n = 0 THEN <>(x = 1) ELSE F(n - 1)
Prop == F(100)
====
