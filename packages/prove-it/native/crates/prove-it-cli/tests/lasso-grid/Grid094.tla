---- MODULE Grid094 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 0 /\ y = 1 /\ x' \in {0, 2} /\ y' = y
A1 == x = 1 /\ y = 0 /\ x' = 0 /\ y' = y
A2 == y = 0 /\ x' \in {1, 2} /\ y' = y
A3 == x = 0 /\ x' = 1 /\ y' = 1
Next == A0 \/ A1 \/ A2 \/ A3
Spec == Init /\ [][Next]_vars /\ WF_vars(A1) /\ WF_vars(A2)
P0 == []((x = 0) => <>[](y = 1))
====
