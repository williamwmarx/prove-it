---- MODULE MRecordsFcnEmptyKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = [i \in {1} |-> [a |-> 0]]
Next == x' \in [{1} -> ([a : {}])] \/ x' = [i \in {1} |-> [a |-> 0]] \/ x' = [i \in {1} |-> [a |-> 2]]
Alias == Next
Weak == Init /\ [][Next]_x /\ WF_x(Next)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Alias)
Live == []<>(x = [i \in {1} |-> [a |-> 0]])
====
