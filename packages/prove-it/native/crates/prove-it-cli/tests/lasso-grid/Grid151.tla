---- MODULE Grid151 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 2 /\ x' \in {1, 2} /\ y' = 1
A1 == x' = 2 /\ y' = (y + 1) % 2
A2 == x = 2 /\ y = 1 /\ x' = x /\ y' = (y + 1) % 2
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == <>[](x = 1)
====
