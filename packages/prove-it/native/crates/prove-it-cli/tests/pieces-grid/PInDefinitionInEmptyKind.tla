---- MODULE PInDefinitionInEmptyKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = 0
A == x' \in (D)
B == x' = 0
E == x' = 2
Next == /\ (A \/ B \/ E)
Copy == x' \in (D)
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = 0)
====
