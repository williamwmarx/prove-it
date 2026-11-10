---- MODULE Grid034 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x = 0 /\ x' = x /\ y' = (y + 1) % 2
A1 == y = 1 /\ x' = 0 /\ y' = 1
A2 == y = 1 /\ x' = 1 /\ y' \in {0, 1}
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []((x = 0) => <>[](y = 1))
P1 == (x = 2) ~> (y = 0)
====
