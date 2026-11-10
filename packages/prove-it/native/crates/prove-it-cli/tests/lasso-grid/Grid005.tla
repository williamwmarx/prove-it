---- MODULE Grid005 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x # 0 /\ y = 1 /\ x' = 1 /\ y' = (y + 1) % 2
A1 == x' = (x + 1) % 3 /\ y' = 1
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ TRUE
P0 == <>[](x = 1)
====
