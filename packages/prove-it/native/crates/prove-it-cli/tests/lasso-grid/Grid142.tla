---- MODULE Grid142 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x = 1 /\ x' \in {1, 2} /\ y' = 0
A1 == y = 1 /\ x' = 0 /\ y' = 0
A2 == x = 1 /\ x' = 2 /\ y' = (y + 1) % 2
A3 == x # 0 /\ x' = (x + 1) % 3 /\ y' = 1
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ A2 \/ A3 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(x # 0)
P1 == []<>(y = 1)
====
