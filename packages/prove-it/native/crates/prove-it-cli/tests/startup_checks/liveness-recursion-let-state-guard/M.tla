---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Prop == LET RECURSIVE F(_)
            F(n) == IF x = 0 THEN <>(x = 1) ELSE (<>(x = 1) /\ F(n + 1))
        IN F(0)
====
