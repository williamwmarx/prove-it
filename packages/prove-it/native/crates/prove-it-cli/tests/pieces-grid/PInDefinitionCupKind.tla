---- MODULE PInDefinitionCupKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = 0
A == x' \in (D) \cup {7}
B == x' = 0
E == x' = 2
Next == /\ (A \/ B \/ E)
Copy == x' \in (D) \cup {7}
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = 0)
====
