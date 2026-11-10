---- MODULE IFilter ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x \in ({y \in {1, 3} : y > 1}) \cup {0}
Next == x' = 0 \/ x' = 2
Alias == Next
Weak == Init /\ [][Next]_x /\ WF_x(Next)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Alias)
Live == <>[](x = 0)
====
