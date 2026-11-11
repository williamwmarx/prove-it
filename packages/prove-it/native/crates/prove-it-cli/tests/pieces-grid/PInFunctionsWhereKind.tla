---- MODULE PInFunctionsWhereKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = [i \in {1} |-> 0]
A == x' \in {z \in ([{1} -> {1, 3}]) : TRUE}
B == x' = [i \in {1} |-> 0]
E == x' = [i \in {1} |-> 2]
Next == /\ (A \/ B \/ E)
Copy == x' \in {z \in ([{1} -> {1, 3}]) : TRUE}
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = [i \in {1} |-> 0])
====
