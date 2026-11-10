---- MODULE Grid100 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x = 2 /\ x' = x /\ y' = 0
A1 == x = 2 /\ x' = x /\ y' = (y + 1) % 2
A2 == x' = x /\ y' = 1
A3 == x = 2 /\ x' = 1 /\ y' = 1
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(y = 1)
====
