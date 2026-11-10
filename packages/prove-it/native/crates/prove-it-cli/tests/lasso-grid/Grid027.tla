---- MODULE Grid027 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x = 1 /\ x' = (x + 1) % 3 /\ y' = y
A1 == x' \in {1, 2} /\ y' = 0
A2 == x = 1 /\ x' = 1 /\ y' = (y + 1) % 2
A3 == x # 2 /\ y = 1 /\ x' = (x + 1) % 3 /\ y' \in {0, 1}
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == (x = 2) ~> (y = 0)
====
