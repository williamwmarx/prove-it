---- MODULE MRecordsRcdEmptyKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = [a |-> [a |-> 0]]
Next == x' \in [a : ([a : {}])] \/ x' = [a |-> [a |-> 0]] \/ x' = [a |-> [a |-> 2]]
Alias == Next
Weak == Init /\ [][Next]_x /\ WF_x(Next)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Alias)
Live == []<>(x = [a |-> [a |-> 0]])
====
