---- MODULE MRecordsRcdKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = [a |-> [a |-> 0]]
Next == x' \in [a : ([a : {1, 3}])] \/ x' = [a |-> [a |-> 0]] \/ x' = [a |-> [a |-> 2]]
Alias == Next
Weak == Init /\ [][Next]_x /\ WF_x(Next)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Alias)
Live == []<>(x = [a |-> [a |-> 0]])
====
