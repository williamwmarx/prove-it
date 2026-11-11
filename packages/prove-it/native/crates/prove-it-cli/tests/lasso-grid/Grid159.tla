---- MODULE Grid159 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x = 2 /\ x' = (x + 1) % 3 /\ y' = y
A1 == x = 2 /\ y = 0 /\ x' \in {1, 2} /\ y' = y
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == (x = 2) ~> (y = 0)
====
