---- MODULE Grid074 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x # 2 /\ x' \in {0, 1} /\ y' = y
A1 == x = 0 /\ x' = (x + 1) % 3 /\ y' = 1
A2 == x' = 1 /\ y' = (y + 1) % 2
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == (x = 2) ~> (y = 0)
P1 == []((x = 0) => <>[](y = 1))
====
