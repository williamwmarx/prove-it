---- MODULE MFunctionsRcdEmptyKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = [a |-> [i \in {1} |-> 0]]
Next == x' \in [a : ([{1} -> {}])] \/ x' = [a |-> [i \in {1} |-> 0]] \/ x' = [a |-> [i \in {1} |-> 2]]
Alias == Next
Weak == Init /\ [][Next]_x /\ WF_x(Next)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Alias)
Live == []<>(x = [a |-> [i \in {1} |-> 0]])
====
