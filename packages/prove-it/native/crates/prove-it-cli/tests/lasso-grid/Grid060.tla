---- MODULE Grid060 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x' \in {0, 1} /\ y' \in {0, 1}
A1 == x' = 1 /\ y' = 1
A2 == x # 0 /\ x' \in {1, 2} /\ y' = (y + 1) % 2
A3 == y = 0 /\ x' = 1 /\ y' = 0
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ A2 \/ A3 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ WF_vars(A1) /\ WF_vars(A3)
P0 == []<>(y = 1)
====
