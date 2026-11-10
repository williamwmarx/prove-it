---- MODULE Grid110 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x = 2 /\ y = 0 /\ x' = 0 /\ y' = (y + 1) % 2
A1 == y = 1 /\ x' \in {0, 1} /\ y' \in {0, 1}
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ WF_vars(A0) /\ WF_vars(A0)
P0 == []<>(x = 0)
====
