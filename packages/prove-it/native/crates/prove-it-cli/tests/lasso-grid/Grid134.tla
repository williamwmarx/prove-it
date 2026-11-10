---- MODULE Grid134 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x' = (x + 1) % 3 /\ y' = y
A1 == x' = (x + 1) % 3 /\ y' = y
A2 == y = 0 /\ x' = (x + 1) % 3 /\ y' = (y + 1) % 2
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == (x = 2) ~> (y = 0)
====
