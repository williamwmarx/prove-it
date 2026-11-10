---- MODULE MSubsetCupKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = {0}
Next == x' \in (SUBSET {1, 3}) \cup {7} \/ x' = {0} \/ x' = {2}
Alias == Next
Weak == Init /\ [][Next]_x /\ WF_x(Next)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Alias)
Live == []<>(x = {0})
====
