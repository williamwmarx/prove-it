---- MODULE Grid136 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 1 /\ y = 1 /\ x' = x /\ y' = 1
A1 == x = 0 /\ y = 0 /\ x' = 1 /\ y' = y
A2 == x' = 0 /\ y' = 0
Next == A0 \/ A1 \/ A2
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == []<>(x = 1 /\ y = 1)
P1 == <>[](x = 1)
====
