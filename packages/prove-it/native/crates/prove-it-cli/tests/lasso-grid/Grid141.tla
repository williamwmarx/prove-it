---- MODULE Grid141 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x' \in {1, 2} /\ y' = (y + 1) % 2
A1 == x' = 1 /\ y' \in {0, 1}
A2 == x' = (x + 1) % 3 /\ y' \in {0, 1}
A3 == x = 2 /\ x' = 0 /\ y' = 0
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == <>[](x = 1)
====
