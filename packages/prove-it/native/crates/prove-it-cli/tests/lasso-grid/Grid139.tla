---- MODULE Grid139 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x = 0 /\ y \in {0, 1}
A0 == x = 1 /\ x' = (x + 1) % 3 /\ y' = (y + 1) % 2
A1 == y = 0 /\ x' = (x + 1) % 3 /\ y' = 1
Next == A0 \/ A1
Spec == Init /\ [][Next]_vars /\ WF_vars(A1) /\ WF_vars(A0)
P0 == <>[](y = 0) \/ []<>(x = 2)
====
