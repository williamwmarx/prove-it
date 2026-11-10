---- MODULE Grid155 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x = 2 /\ x' \in {1, 2} /\ y' = (y + 1) % 2
A1 == x = 2 /\ y = 1 /\ x' = x /\ y' = 0
A2 == x = 1 /\ y = 1 /\ x' = (x + 1) % 3 /\ y' = 0
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == <>[](x = 1)
====
