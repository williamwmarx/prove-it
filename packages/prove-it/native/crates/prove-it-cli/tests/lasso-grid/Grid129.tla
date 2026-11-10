---- MODULE Grid129 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x # 0 /\ x' \in {1, 2} /\ y' = 0
A1 == x' = x /\ y' = 1
A2 == x # 1 /\ y = 1 /\ x' = x /\ y' \in {0, 1}
A3 == x = 1 /\ x' = (x + 1) % 3 /\ y' = y
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ WF_vars(A3) /\ WF_vars(A1)
P0 == []<>(x = 1 /\ y = 1)
P1 == <>[](x = 1)
====
