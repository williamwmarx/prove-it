---- MODULE Grid002 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == y = 1 /\ x' = (x + 1) % 3 /\ y' = y
A1 == x' = 0 /\ y' = 1
A2 == x # 2 /\ y = 1 /\ x' = 0 /\ y' \in {0, 1}
A3 == x' = (x + 1) % 3 /\ y' = (y + 1) % 2
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == (x = 2) ~> (y = 0)
P1 == <>[](x = 1)
====
