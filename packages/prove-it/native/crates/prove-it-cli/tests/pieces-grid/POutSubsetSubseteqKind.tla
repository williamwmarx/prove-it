---- MODULE POutSubsetSubseteqKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = {{0}}
A == x' \subseteq (SUBSET {1, 3})
B == x' = {{0}}
E == x' = {{2}}
Next == /\ (A \/ B \/ E)
Copy == x' = {{0}}
Weak == Init /\ [][Next]_x /\ WF_x(B)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = {{0}})
====
