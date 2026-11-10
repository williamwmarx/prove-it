---- MODULE Grid123 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x' = x /\ y' = 1
A1 == y = 0 /\ x' = 1 /\ y' = y
A2 == x' = (x + 1) % 3 /\ y' = 0
A3 == x = 0 /\ x' = 0 /\ y' = 1
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ WF_vars(A3) /\ WF_vars(A1)
P0 == []<>(x = 0)
P1 == []<>(y = 1)
====
