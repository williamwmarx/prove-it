---- MODULE Grid144 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x = 0 /\ x' = 0 /\ y' = (y + 1) % 2
A1 == x' \in {0, 1} /\ y' = 0
A2 == x # 0 /\ x' = x /\ y' \in {0, 1}
A3 == x # 0 /\ y = 1 /\ x' \in {0, 1} /\ y' = y
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ WF_vars(A2) /\ WF_vars(A2)
P0 == []<>(x # 0)
====
