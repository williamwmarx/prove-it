---- MODULE PInFilterSubseteq ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = 0
A == x' \subseteq ({y \in {1, 3} : y > 1})
B == x' = 0
E == x' = 1
Next == /\ (A \/ B \/ E)
Copy == x' \subseteq ({y \in {1, 3} : y > 1})
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = 0)
====
