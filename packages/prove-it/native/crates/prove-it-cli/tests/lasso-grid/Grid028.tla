---- MODULE Grid028 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == y = 1 /\ x' = 2 /\ y' = 1
A1 == x' \in {0, 2} /\ y' \in {0, 1}
A2 == x' = x /\ y' = 0
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(x = 1 /\ y = 1)
====
