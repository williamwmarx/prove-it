---- MODULE Grid001 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == y = 1 /\ x' = x /\ y' = 0
A1 == x' = (x + 1) % 3 /\ y' = 0
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == <>[](y = 0) \/ []<>(x = 2)
P1 == []<>(x # 0)
====
