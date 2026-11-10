---- MODULE Grid157 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x = 2 /\ y = 0 /\ x' = 1 /\ y' \in {0, 1}
A1 == x = 2 /\ x' = (x + 1) % 3 /\ y' \in {0, 1}
A2 == x' = x /\ y' = 1
A3 == x = 2 /\ x' = (x + 1) % 3 /\ y' = y
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ WF_vars(A0) /\ WF_vars(A2)
P0 == <>[](y = 0) \/ []<>(x = 2)
P1 == []<>(y = 1)
====
