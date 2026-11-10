---- MODULE Grid046 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x' = (x + 1) % 3 /\ y' = y
A1 == x = 0 /\ y = 0 /\ x' \in {0, 2} /\ y' = 0
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == []<>(x = 0)
====
