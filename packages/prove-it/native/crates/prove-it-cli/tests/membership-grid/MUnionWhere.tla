---- MODULE MUnionWhere ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = 0
Next == x' \in {z \in ({1} \cup {3}) : TRUE} \/ x' = 0 \/ x' = 1
Alias == Next
Weak == Init /\ [][Next]_x /\ WF_x(Next)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Alias)
Live == []<>(x = 0)
====
