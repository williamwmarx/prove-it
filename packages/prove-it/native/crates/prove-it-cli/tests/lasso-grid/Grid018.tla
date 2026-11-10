---- MODULE Grid018 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x' = 1 /\ y' = 0
A1 == x = 0 /\ x' = (x + 1) % 3 /\ y' \in {0, 1}
A2 == x' = x /\ y' = y
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == []<>(x # 0)
P1 == (x = 2) ~> (y = 0)
====
