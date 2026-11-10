---- MODULE Grid112 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x' = (x + 1) % 3 /\ y' = (y + 1) % 2
A1 == x = 0 /\ y = 1 /\ x' = 1 /\ y' = 1
A2 == x # 1 /\ x' = (x + 1) % 3 /\ y' = (y + 1) % 2
A3 == x = 1 /\ y = 1 /\ x' = (x + 1) % 3 /\ y' = (y + 1) % 2
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == []<>(y = 1)
====
