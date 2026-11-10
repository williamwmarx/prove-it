---- MODULE MUnionWhereEmptyKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = 0
Next == x' \in {z \in ({} \cup {}) : TRUE} \/ x' = 0 \/ x' = 2
Alias == Next
Weak == Init /\ [][Next]_x /\ WF_x(Next)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Alias)
Live == []<>(x = 0)
====
