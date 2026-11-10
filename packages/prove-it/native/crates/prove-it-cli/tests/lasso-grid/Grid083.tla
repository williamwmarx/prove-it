---- MODULE Grid083 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x = 0 /\ x' \in {0, 1} /\ y' = y
A1 == x = 2 /\ x' = 0 /\ y' = 0
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == []<>(x # 0)
P1 == []<>(x = 1 /\ y = 1)
====
