---- MODULE Grid148 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == y = 1 /\ x' = x /\ y' = 1
A1 == x = 1 /\ x' = x /\ y' = 1
A2 == x = 0 /\ x' = 1 /\ y' = y
A3 == x # 1 /\ x' = x /\ y' = (y + 1) % 2
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == []((x = 0) => <>[](y = 1))
P1 == []<>(x = 0)
====
