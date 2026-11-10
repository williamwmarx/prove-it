---- MODULE Grid003 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == y = 0 /\ x' = 2 /\ y' = 0
A1 == x = 0 /\ x' \in {0, 2} /\ y' = y
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ WF_vars(A1) /\ WF_vars(A0)
P0 == <>[](x = 1)
====
