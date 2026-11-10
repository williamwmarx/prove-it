---- MODULE Grid078 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x = 0 /\ y = 1 /\ x' = 2 /\ y' = 1
A1 == x = 1 /\ x' = 1 /\ y' = y
A2 == x = 0 /\ x' = 2 /\ y' = (y + 1) % 2
A3 == x # 2 /\ x' = 0 /\ y' = 0
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ A2 \/ A3 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == []<>(x = 1 /\ y = 1)
====
