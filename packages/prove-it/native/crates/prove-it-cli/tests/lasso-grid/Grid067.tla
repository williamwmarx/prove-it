---- MODULE Grid067 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x' = (x + 1) % 3 /\ y' \in {0, 1}
A1 == x' \in {0, 2} /\ y' = y
A2 == x = 0 /\ y = 1 /\ x' \in {1, 2} /\ y' = 1
A3 == x # 0 /\ x' \in {1, 2} /\ y' = 0
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == (x = 2) ~> (y = 0)
====
