---- MODULE Grid089 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x' = x /\ y' = 0
A1 == x' = (x + 1) % 3 /\ y' = y
A2 == x' \in {0, 1} /\ y' = 1
A3 == x' = 2 /\ y' = 0
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ A2 \/ A3 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(x # 0)
P1 == <>[](y = 0) \/ []<>(x = 2)
====
