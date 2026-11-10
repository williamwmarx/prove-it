---- MODULE IConstant ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x \in (C) \cup {0}
Next == x' = 0 \/ x' = 2
Alias == Next
Weak == Init /\ [][Next]_x /\ WF_x(Next)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Alias)
Live == <>[](x = 0)
====
