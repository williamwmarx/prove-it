---- MODULE Grid055 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x = 2 /\ x' = 1 /\ y' = y
A1 == x' = 0 /\ y' = y
A2 == x = 0 /\ x' = (x + 1) % 3 /\ y' = 0
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ A2 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == <>[](y = 0) \/ []<>(x = 2)
P1 == []<>(x = 0)
====
