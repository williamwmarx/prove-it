---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
RECURSIVE F(_, _)
F(n, b) == IF n = 0 THEN <>(x = 1) ELSE (<>(x = 2) /\ F(n - 1, b))
Prop == F(3, \A i, j, k \in 1..1000 : TRUE)
====
