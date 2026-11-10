---- MODULE Grid109 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in {0, 1} /\ y = 0
A0 == x # 2 /\ y = 1 /\ x' \in {1, 2} /\ y' = (y + 1) % 2
A1 == x = 2 /\ y = 1 /\ x' = (x + 1) % 3 /\ y' = (y + 1) % 2
A2 == x = 1 /\ x' = x /\ y' \in {0, 1}
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(A2) /\ WF_vars(A1)
P0 == (x = 2) ~> (y = 0)
====
