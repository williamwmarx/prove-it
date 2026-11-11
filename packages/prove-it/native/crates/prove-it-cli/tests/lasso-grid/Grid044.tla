---- MODULE Grid044 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x' = 0 /\ y' = (y + 1) % 2
A1 == x = 1 /\ x' \in {1, 2} /\ y' = 1
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == <>[](x = 1)
====
