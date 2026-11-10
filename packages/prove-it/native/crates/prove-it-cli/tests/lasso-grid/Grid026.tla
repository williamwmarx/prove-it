---- MODULE Grid026 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 0 /\ y = 0 /\ x' = x /\ y' \in {0, 1}
A1 == x = 0 /\ x' = (x + 1) % 3 /\ y' = (y + 1) % 2
A2 == x = 1 /\ x' = x /\ y' = y
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(y = 1)
====
