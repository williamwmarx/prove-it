---- MODULE POutFunctionsRcdEmptyKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = [a |-> [i \in {1} |-> 0]]
A == x' \in [a : ([{1} -> {}])]
B == x' = [a |-> [i \in {1} |-> 0]]
E == x' = [a |-> [i \in {1} |-> 2]]
Next == /\ (A \/ B \/ E)
Copy == x' = [a |-> [i \in {1} |-> 0]]
Weak == Init /\ [][Next]_x /\ WF_x(B)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = [a |-> [i \in {1} |-> 0]])
====
