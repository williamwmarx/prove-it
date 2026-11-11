---- MODULE PInFunctionsSubseteqEmptyKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = {[i \in {1} |-> 0]}
A == x' \subseteq ([{1} -> {}])
B == x' = {[i \in {1} |-> 0]}
E == x' = {[i \in {1} |-> 2]}
Next == /\ (A \/ B \/ E)
Copy == x' \subseteq ([{1} -> {}])
Weak == Init /\ [][Next]_x /\ WF_x(A)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Copy)
Live == []<>(x = {[i \in {1} |-> 0]})
====
