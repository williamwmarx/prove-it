---- MODULE Grid132 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x = 1 /\ x' \in {0, 1} /\ y' \in {0, 1}
A1 == x = 1 /\ x' \in {0, 2} /\ y' = 0
A2 == x # 1 /\ y = 0 /\ x' = (x + 1) % 3 /\ y' = (y + 1) % 2
A3 == x' = (x + 1) % 3 /\ y' = (y + 1) % 2
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ A2 \/ A3 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == []((x = 0) => <>[](y = 1))
P1 == (x = 2) ~> (y = 0)
====
