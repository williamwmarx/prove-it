---- MODULE Grid138 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x' \in {1, 2} /\ y' = (y + 1) % 2
A1 == x = 0 /\ y = 0 /\ x' = (x + 1) % 3 /\ y' = y
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == <>[](y = 0) \/ []<>(x = 2)
P1 == []<>(x # 0)
====
