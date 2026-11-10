---- MODULE Grid009 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x # 2 /\ y = 1 /\ x' \in {1, 2} /\ y' \in {0, 1}
A1 == x # 0 /\ y = 0 /\ x' \in {0, 1} /\ y' = 0
A2 == x # 2 /\ x' \in {0, 2} /\ y' = 0
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(x = 1 /\ y = 1)
P1 == []<>(y = 1)
====
