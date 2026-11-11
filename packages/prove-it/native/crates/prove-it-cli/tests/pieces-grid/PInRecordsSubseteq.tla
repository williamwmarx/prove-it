---- MODULE PInRecordsSubseteq ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = 0
A == x' \subseteq ([a : {1, 3}])
B == x' = 0
E == x' = 1
Next == /\ (A \/ B \/ E)
Copy == x' \subseteq ([a : {1, 3}])
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = 0)
====
