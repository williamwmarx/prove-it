---- MODULE Grid065 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x = 1 /\ x' \in {0, 1} /\ y' \in {0, 1}
A1 == x = 2 /\ x' \in {0, 1} /\ y' = y
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(y = 1)
P1 == (x = 2) ~> (y = 0)
====
