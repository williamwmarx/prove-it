---- MODULE Grid096 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == y = 0 /\ x' = 1 /\ y' = 0
A1 == x' = x /\ y' = 0
A2 == x' = 1 /\ y' = 0
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == (x = 2) ~> (y = 0)
====
