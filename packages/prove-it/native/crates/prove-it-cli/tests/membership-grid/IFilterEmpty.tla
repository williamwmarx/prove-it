---- MODULE IFilterEmpty ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x \in ({y \in {1, 3} : y > 5}) \cup {0}
Next == x' = 0 \/ x' = 2
Alias == Next
Weak == Init /\ [][Next]_x /\ WF_x(Next)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Alias)
Live == <>[](x = 0)
====
