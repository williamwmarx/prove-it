---- MODULE Grid016 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x # 1 /\ x' = 0 /\ y' = 0
A1 == x # 1 /\ x' \in {1, 2} /\ y' = (y + 1) % 2
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(y = 1)
====
