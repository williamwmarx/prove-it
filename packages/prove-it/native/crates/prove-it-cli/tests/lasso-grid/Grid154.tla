---- MODULE Grid154 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x' \in {0, 2} /\ y' = (y + 1) % 2
A1 == y = 1 /\ x' = (x + 1) % 3 /\ y' = 0
A2 == x = 1 /\ x' = 2 /\ y' = 0
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(x # 0)
P1 == []<>(x = 1 /\ y = 1)
====
