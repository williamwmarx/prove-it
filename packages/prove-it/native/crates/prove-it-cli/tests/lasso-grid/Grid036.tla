---- MODULE Grid036 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x' = x /\ y' \in {0, 1}
A1 == x = 2 /\ y = 1 /\ x' = 1 /\ y' \in {0, 1}
A2 == x' = (x + 1) % 3 /\ y' = y
A3 == x # 2 /\ x' = 1 /\ y' = 1
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == []((x = 0) => <>[](y = 1))
====
