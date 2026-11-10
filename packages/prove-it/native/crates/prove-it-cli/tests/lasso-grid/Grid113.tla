---- MODULE Grid113 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x # 2 /\ x' = x /\ y' \in {0, 1}
A1 == x = 1 /\ y = 0 /\ x' = 2 /\ y' = (y + 1) % 2
A2 == x' = (x + 1) % 3 /\ y' = y
A3 == x' = 2 /\ y' = (y + 1) % 2
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == (x = 2) ~> (y = 0)
====
