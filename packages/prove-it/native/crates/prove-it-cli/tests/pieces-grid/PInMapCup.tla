---- MODULE PInMapCup ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = 0
A == x' \in ({y + 1 : y \in {1, 3}}) \cup {7}
B == x' = 0
E == x' = 1
Next == /\ (A \/ B \/ E)
Copy == x' \in ({y + 1 : y \in {1, 3}}) \cup {7}
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = 0)
====
