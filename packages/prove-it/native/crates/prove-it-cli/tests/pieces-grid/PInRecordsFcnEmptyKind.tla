---- MODULE PInRecordsFcnEmptyKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = [i \in {1} |-> [a |-> 0]]
A == x' \in [{1} -> ([a : {}])]
B == x' = [i \in {1} |-> [a |-> 0]]
E == x' = [i \in {1} |-> [a |-> 2]]
Next == /\ (A \/ B \/ E)
Copy == x' \in [{1} -> ([a : {}])]
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = [i \in {1} |-> [a |-> 0]])
====
