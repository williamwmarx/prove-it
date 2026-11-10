---- MODULE Grid085 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == y = 1 /\ x' \in {1, 2} /\ y' = y
A1 == x = 0 /\ y = 0 /\ x' = (x + 1) % 3 /\ y' = 1
A2 == x # 1 /\ y = 0 /\ x' = 0 /\ y' = 1
A3 == x = 2 /\ y = 1 /\ x' \in {1, 2} /\ y' = (y + 1) % 2
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(x = 0)
====
