---- MODULE Grid128 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 2 /\ x' = 2 /\ y' = y
A1 == x # 2 /\ x' = (x + 1) % 3 /\ y' = y
A2 == x # 1 /\ y = 0 /\ x' = 0 /\ y' \in {0, 1}
A3 == x = 1 /\ x' = x /\ y' = y
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == []<>(x = 1 /\ y = 1)
P1 == <>[](y = 0) \/ []<>(x = 2)
====
