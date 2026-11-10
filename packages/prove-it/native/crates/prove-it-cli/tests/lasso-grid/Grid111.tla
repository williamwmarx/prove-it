---- MODULE Grid111 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x = 2 /\ x' = (x + 1) % 3 /\ y' = 1
A1 == x = 1 /\ x' = (x + 1) % 3 /\ y' = y
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ WF_vars(A0) /\ WF_vars(A0)
P0 == []<>(x = 0)
====
