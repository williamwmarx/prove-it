---- MODULE Grid063 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x = 2 /\ x' = x /\ y' = (y + 1) % 2
A1 == y = 0 /\ x' = 1 /\ y' \in {0, 1}
A2 == x # 2 /\ y = 0 /\ x' = x /\ y' = (y + 1) % 2
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == []<>(y = 1)
====
