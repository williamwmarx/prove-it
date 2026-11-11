---- MODULE POutConstantCupEmptyKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = 0
A == x' \in (C) \cup {7}
B == x' = 0
E == x' = 2
Next == /\ (A \/ B \/ E)
Copy == x' = 0
Weak == Init /\ [][Next]_x /\ WF_x(B)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = 0)
====
