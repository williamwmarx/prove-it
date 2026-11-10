---- MODULE Grid011 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x # 1 /\ x' = x /\ y' = 0
A1 == x # 0 /\ x' = x /\ y' \in {0, 1}
A2 == x # 2 /\ x' = (x + 1) % 3 /\ y' = 0
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(x # 0)
P1 == <>[](y = 0) \/ []<>(x = 2)
====
