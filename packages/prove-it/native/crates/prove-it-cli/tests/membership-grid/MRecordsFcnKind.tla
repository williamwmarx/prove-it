---- MODULE MRecordsFcnKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = [i \in {1} |-> [a |-> 0]]
Next == x' \in [{1} -> ([a : {1, 3}])] \/ x' = [i \in {1} |-> [a |-> 0]] \/ x' = [i \in {1} |-> [a |-> 2]]
Alias == Next
Weak == Init /\ [][Next]_x /\ WF_x(Next)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Alias)
Live == []<>(x = [i \in {1} |-> [a |-> 0]])
====
