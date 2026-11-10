---- MODULE Grid118 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 1 /\ x' = (x + 1) % 3 /\ y' = 0
A1 == x = 0 /\ y = 0 /\ x' = (x + 1) % 3 /\ y' = y
A2 == y = 0 /\ x' = 1 /\ y' = (y + 1) % 2
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == <>[](y = 0) \/ []<>(x = 2)
====
