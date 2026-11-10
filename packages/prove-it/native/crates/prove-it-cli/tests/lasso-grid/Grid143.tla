---- MODULE Grid143 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x = 2 /\ x' = 2 /\ y' \in {0, 1}
A1 == x' = x /\ y' = 0
A2 == x = 1 /\ x' = x /\ y' = 1
A3 == x = 1 /\ x' = 0 /\ y' \in {0, 1}
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ WF_vars(A3) /\ WF_vars(A2)
P0 == []<>(x = 0)
====
