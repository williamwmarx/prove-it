---- MODULE Grid116 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x' = (x + 1) % 3 /\ y' = 0
A1 == x = 2 /\ x' = 0 /\ y' = 1
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == <>[](y = 0) \/ []<>(x = 2)
====
