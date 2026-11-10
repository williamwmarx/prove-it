---- MODULE Grid087 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x' = x /\ y' \in {0, 1}
A1 == x' = 0 /\ y' = 0
A2 == x # 0 /\ x' = x /\ y' = y
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ A2 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ WF_vars(A0) /\ WF_vars(A2)
P0 == []<>(y = 1)
====
