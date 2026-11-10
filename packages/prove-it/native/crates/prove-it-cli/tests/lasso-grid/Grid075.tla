---- MODULE Grid075 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 2 /\ y = 0 /\ x' = 2 /\ y' = y
A1 == x # 0 /\ y = 0 /\ x' \in {0, 1} /\ y' = 0
A2 == x' = 2 /\ y' = y
A3 == y = 1 /\ x' \in {0, 2} /\ y' = y
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ WF_vars(A0) /\ WF_vars(A1)
P0 == []<>(x # 0)
P1 == <>[](x = 1)
====
