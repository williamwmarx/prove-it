---- MODULE POutIntervalFcnEmptyKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = [i \in {1} |-> 0]
A == x' \in [{1} -> (1..0)]
B == x' = [i \in {1} |-> 0]
E == x' = [i \in {1} |-> 2]
Next == /\ (A \/ B \/ E)
Copy == x' = [i \in {1} |-> 0]
Weak == Init /\ [][Next]_x /\ WF_x(B)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = [i \in {1} |-> 0])
====
