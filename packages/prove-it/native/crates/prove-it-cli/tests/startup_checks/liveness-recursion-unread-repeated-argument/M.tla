---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
RECURSIVE F(_, _)
F(a, n) == IF n = 0 THEN <>(x = 1) ELSE (a /\ F(\A i, j, k \in 1..1000 : TRUE, n - 1))
Prop == F(1 = 1, 1)
====
