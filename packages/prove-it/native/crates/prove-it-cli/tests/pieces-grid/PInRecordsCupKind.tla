---- MODULE PInRecordsCupKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = [a |-> 0]
A == x' \in ([a : {1, 3}]) \cup {7}
B == x' = [a |-> 0]
E == x' = [a |-> 2]
Next == /\ (A \/ B \/ E)
Copy == x' \in ([a : {1, 3}]) \cup {7}
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = [a |-> 0])
====
