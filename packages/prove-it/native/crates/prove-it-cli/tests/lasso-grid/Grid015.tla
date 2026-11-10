---- MODULE Grid015 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x = 2 /\ x' \in {0, 1} /\ y' = 0
A1 == x = 1 /\ y = 1 /\ x' = x /\ y' = y
A2 == x = 0 /\ x' = 0 /\ y' = y
B(i) == x = i /\ x' = (i + 1) % 3 /\ y' = 1 - y
Next == A0 \/ A1 \/ A2 \/ \E i \in {0, 1} : B(i)
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == []<>(x = 0)
P1 == <>[](x = 1)
====
