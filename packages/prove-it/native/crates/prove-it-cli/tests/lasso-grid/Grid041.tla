---- MODULE Grid041 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x = 2 /\ y = 1 /\ x' \in {0, 1} /\ y' = 1
A1 == x = 1 /\ x' = (x + 1) % 3 /\ y' = y
A2 == x' = (x + 1) % 3 /\ y' = 1
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(x = 1 /\ y = 1)
====
