---- MODULE Grid008 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x = 1 /\ x' = 2 /\ y' \in {0, 1}
A1 == x = 2 /\ x' \in {0, 1} /\ y' = y
A2 == x = 0 /\ x' = 0 /\ y' = 1
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(A0) /\ WF_vars(A0)
P0 == []<>(x = 1 /\ y = 1)
P1 == <>[](x = 1)
====
