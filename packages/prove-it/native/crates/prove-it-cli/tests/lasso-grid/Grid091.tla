---- MODULE Grid091 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 0 /\ y = 0 /\ x' = (x + 1) % 3 /\ y' = y
A1 == x = 0 /\ y = 1 /\ x' = x /\ y' \in {0, 1}
A2 == x' = (x + 1) % 3 /\ y' \in {0, 1}
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == []<>(x = 1 /\ y = 1)
P1 == []<>(y = 1)
====
