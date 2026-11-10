---- MODULE Grid050 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x = 0 /\ y = 0 /\ x' = x /\ y' = 0
A1 == x' = (x + 1) % 3 /\ y' = y
A2 == x' = (x + 1) % 3 /\ y' = y
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == []<>(x = 1 /\ y = 1)
====
