---- MODULE Grid045 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == y = 1 /\ x' \in {0, 1} /\ y' = y
A1 == y = 1 /\ x' = 2 /\ y' = (y + 1) % 2
A2 == x = 2 /\ x' = (x + 1) % 3 /\ y' \in {0, 1}
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(x # 0)
====
