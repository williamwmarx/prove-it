---- MODULE PInUnionSubseteqKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = {0}
A == x' \subseteq ({1} \cup {3})
B == x' = {0}
E == x' = {2}
Next == /\ (A \/ B \/ E)
Copy == x' \subseteq ({1} \cup {3})
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = {0})
====
