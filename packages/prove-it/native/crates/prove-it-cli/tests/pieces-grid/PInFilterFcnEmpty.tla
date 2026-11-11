---- MODULE PInFilterFcnEmpty ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = 0
A == x' \in [{1} -> ({y \in {1, 3} : y > 5})]
B == x' = 0
E == x' = 1
Next == /\ (A \/ B \/ E)
Copy == x' \in [{1} -> ({y \in {1, 3} : y > 5})]
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = 0)
====
