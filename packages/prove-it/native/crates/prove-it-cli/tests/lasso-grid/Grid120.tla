---- MODULE Grid120 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x' \in {0, 2} /\ y' = y
A1 == x # 0 /\ x' = x /\ y' = 0
A2 == x = 1 /\ x' = 0 /\ y' = (y + 1) % 2
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == <>[](x = 1)
====
