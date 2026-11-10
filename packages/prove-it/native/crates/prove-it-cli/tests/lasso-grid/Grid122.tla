---- MODULE Grid122 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x # 2 /\ x' = x /\ y' = 0
A1 == x' = (x + 1) % 3 /\ y' \in {0, 1}
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == []<>(x = 1 /\ y = 1)
====
