---- MODULE Grid024 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == y = 1 /\ x' = (x + 1) % 3 /\ y' = 1
A1 == x = 2 /\ y = 0 /\ x' = x /\ y' = 0
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == []<>(x = 0)
P1 == <>[](x = 1)
====
