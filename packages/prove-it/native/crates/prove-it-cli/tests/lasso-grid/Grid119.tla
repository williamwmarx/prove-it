---- MODULE Grid119 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x' \in {1, 2} /\ y' \in {0, 1}
A1 == x' = (x + 1) % 3 /\ y' = y
A2 == x # 0 /\ x' = x /\ y' \in {0, 1}
A3 == x' = x /\ y' = 0
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(x = 1 /\ y = 1)
====
