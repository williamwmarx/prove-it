---- MODULE PInUnionInEmpty ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = 0
A == x' \in ({} \cup {})
B == x' = 0
E == x' = 1
Next == /\ (A \/ B \/ E)
Copy == x' \in ({} \cup {})
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = 0)
====
