---- MODULE PInRecordsRcdKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = [a |-> [a |-> 0]]
A == x' \in [a : ([a : {1, 3}])]
B == x' = [a |-> [a |-> 0]]
E == x' = [a |-> [a |-> 2]]
Next == /\ (A \/ B \/ E)
Copy == x' \in [a : ([a : {1, 3}])]
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = [a |-> [a |-> 0]])
====
