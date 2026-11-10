---- MODULE Grid088 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A0 == x = 2 /\ x' \in {0, 1} /\ y' = y
A1 == y = 0 /\ x' = x /\ y' = y
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
P0 == <>[](y = 0) \/ []<>(x = 2)
P1 == []<>(x = 1 /\ y = 1)
====
