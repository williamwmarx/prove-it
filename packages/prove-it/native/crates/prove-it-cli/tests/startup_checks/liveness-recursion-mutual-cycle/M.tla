---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
RECURSIVE F(_), G(_)
F(n) == IF x = 2 THEN <>(x = 1) ELSE ([](x # 5) /\ G((n + 1) % 3))
G(n) == F(n)
Prop == F(0)
====
