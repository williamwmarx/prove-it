---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Ignore(a) == TRUE
RECURSIVE F(_)
F(n) == IF FALSE THEN F(n) ELSE ((n /\ <>(x = 1)) \/ <>(x = 2))
Prop == F(Ignore(x))
====
