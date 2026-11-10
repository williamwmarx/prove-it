---- MODULE Grid039 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == y = 1 /\ x' = (x + 1) % 3 /\ y' = (y + 1) % 2
A1 == y = 0 /\ x' = 2 /\ y' = y
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == <>[](y = 0) \/ []<>(x = 2)
P1 == []<>(y = 1)
====
