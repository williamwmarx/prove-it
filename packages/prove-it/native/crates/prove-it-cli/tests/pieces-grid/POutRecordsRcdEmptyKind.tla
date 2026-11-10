---- MODULE POutRecordsRcdEmptyKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = [a |-> [a |-> 0]]
A == x' \in [a : ([a : {}])]
B == x' = [a |-> [a |-> 0]]
E == x' = [a |-> [a |-> 2]]
Next == /\ (A \/ B \/ E)
Copy == x' = [a |-> [a |-> 0]]
Weak == Init /\ [][Next]_x /\ WF_x(B)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = [a |-> [a |-> 0]])
====
