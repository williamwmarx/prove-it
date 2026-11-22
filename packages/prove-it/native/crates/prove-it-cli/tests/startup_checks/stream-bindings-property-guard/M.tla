---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Prop == IF \E i, j, k \in 1..1000 : i = 1 THEN <>(x = 1) ELSE [](x = 0)
====
