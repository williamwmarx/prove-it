---- MODULE Grid095 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == y = 1 /\ x' = 1 /\ y' = y
A1 == x # 2 /\ x' = x /\ y' = (y + 1) % 2
A2 == x = 2 /\ x' \in {0, 2} /\ y' = y
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(x = 0)
P1 == []<>(x = 1 /\ y = 1)
====
