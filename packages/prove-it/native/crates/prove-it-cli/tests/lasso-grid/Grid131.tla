---- MODULE Grid131 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x = 1 /\ x' = 0 /\ y' = (y + 1) % 2
A1 == x = 0 /\ y = 0 /\ x' = (x + 1) % 3 /\ y' \in {0, 1}
A2 == y = 0 /\ x' = (x + 1) % 3 /\ y' \in {0, 1}
A3 == x = 0 /\ y = 1 /\ x' = 0 /\ y' = (y + 1) % 2
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ SF_vars(Next)
P0 == []<>(y = 1)
P1 == []<>(x = 0)
====
