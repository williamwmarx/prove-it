---- MODULE PInConstantFcnKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = [i \in {1} |-> 0]
A == x' \in [{1} -> (C)]
B == x' = [i \in {1} |-> 0]
E == x' = [i \in {1} |-> 2]
Next == /\ (A \/ B \/ E)
Copy == x' \in [{1} -> (C)]
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = [i \in {1} |-> 0])
====
