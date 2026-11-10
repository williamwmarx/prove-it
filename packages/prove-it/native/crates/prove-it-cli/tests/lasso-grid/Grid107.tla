---- MODULE Grid107 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x' = (x + 1) % 3 /\ y' = 1
A1 == y = 0 /\ x' = x /\ y' = 0
A2 == x = 1 /\ x' \in {0, 1} /\ y' = y
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == (x = 2) ~> (y = 0)
P1 == []<>(y = 1)
====
