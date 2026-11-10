---- MODULE MDefinitionInEmpty ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x = 0
Next == x' \in (D) \/ x' = 0 \/ x' = 1
Alias == Next
Weak == Init /\ [][Next]_x /\ WF_x(Next)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Alias)
Live == []<>(x = 0)
====
