---- MODULE Grid140 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 1 /\ y = 1 /\ x' = 0 /\ y' \in {0, 1}
A1 == y = 1 /\ x' = (x + 1) % 3 /\ y' = 0
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ WF_vars(A0) /\ WF_vars(A1)
P0 == []<>(x = 0)
====
