---- MODULE Grid101 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 1 /\ x' = x /\ y' = 1
A1 == x' \in {0, 1} /\ y' = 0
A2 == y = 1 /\ x' = 1 /\ y' = 0
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(A2) /\ WF_vars(A2)
P0 == []<>(x = 1 /\ y = 1)
====
