---- MODULE Grid097 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == y = 0 /\ x' = (x + 1) % 3 /\ y' = 1
A1 == x = 2 /\ y = 0 /\ x' = 1 /\ y' = 0
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == <>[](x = 1)
P1 == []<>(y = 1)
====
