---- MODULE Grid012 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == y = 0 /\ x' \in {0, 1} /\ y' = (y + 1) % 2
A1 == y = 1 /\ x' = 0 /\ y' = (y + 1) % 2
A2 == x = 1 /\ x' = x /\ y' = (y + 1) % 2
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(x = 1 /\ y = 1)
P1 == <>[](x = 1)
====
