---- MODULE Grid070 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 1 /\ y = 0 /\ x' = 0 /\ y' = y
A1 == x = 1 /\ x' = (x + 1) % 3 /\ y' \in {0, 1}
A2 == x = 2 /\ x' = 0 /\ y' = 0
A3 == x' = x /\ y' \in {0, 1}
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == []<>(y = 1)
P1 == (x = 2) ~> (y = 0)
====
