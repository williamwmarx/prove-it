---- MODULE Grid035 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x' = (x + 1) % 3 /\ y' = y
A1 == x # 2 /\ x' = x /\ y' = 1
A2 == x # 0 /\ y = 1 /\ x' = (x + 1) % 3 /\ y' = 1
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(A0) /\ WF_vars(A0)
P0 == []<>(x = 0)
====
