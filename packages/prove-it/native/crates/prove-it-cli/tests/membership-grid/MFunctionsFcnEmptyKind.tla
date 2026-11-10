---- MODULE MFunctionsFcnEmptyKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = [i \in {1} |-> [i \in {1} |-> 0]]
Next == x' \in [{1} -> ([{1} -> {}])] \/ x' = [i \in {1} |-> [i \in {1} |-> 0]] \/ x' = [i \in {1} |-> [i \in {1} |-> 2]]
Alias == Next
Weak == Init /\ [][Next]_x /\ WF_x(Next)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Alias)
Live == []<>(x = [i \in {1} |-> [i \in {1} |-> 0]])
====
