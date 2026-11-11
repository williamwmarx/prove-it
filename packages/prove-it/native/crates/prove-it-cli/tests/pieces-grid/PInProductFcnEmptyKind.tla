---- MODULE PInProductFcnEmptyKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = [i \in {1} |-> <<0, 1>>]
A == x' \in [{1} -> ({} \X {1})]
B == x' = [i \in {1} |-> <<0, 1>>]
E == x' = [i \in {1} |-> <<2, 1>>]
Next == /\ (A \/ B \/ E)
Copy == x' \in [{1} -> ({} \X {1})]
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = [i \in {1} |-> <<0, 1>>])
====
