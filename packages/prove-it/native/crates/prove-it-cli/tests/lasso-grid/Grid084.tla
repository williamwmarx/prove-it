---- MODULE Grid084 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == y = 1 /\ x' = x /\ y' = y
A1 == x' = (x + 1) % 3 /\ y' \in {0, 1}
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == []<>(y = 1)
====
