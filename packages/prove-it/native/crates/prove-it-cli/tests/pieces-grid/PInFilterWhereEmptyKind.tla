---- MODULE PInFilterWhereEmptyKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = 0
A == x' \in {z \in ({y \in {1, 3} : y > 5}) : TRUE}
B == x' = 0
E == x' = 2
Next == /\ (A \/ B \/ E)
Copy == x' \in {z \in ({y \in {1, 3} : y > 5}) : TRUE}
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = 0)
====
