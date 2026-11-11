---- MODULE PInDefinitionSubseteqWrap ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = {0}
A == x' \subseteq (D)
B == x' = {0}
E == x' = {2}
Next == /\ (A \/ B \/ E)
Copy == x' \subseteq (D)
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = {0})
====
