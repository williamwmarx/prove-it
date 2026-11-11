---- MODULE POutIntervalSubseteqEmptyKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = {0}
A == x' \subseteq (1..0)
B == x' = {0}
E == x' = {2}
Next == /\ (A \/ B \/ E)
Copy == x' = {0}
Weak == Init /\ [][Next]_x /\ WF_x(B)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = {0})
====
