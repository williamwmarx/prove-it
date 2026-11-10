---- MODULE IRecordsEmpty ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {}
Init == x \in ([a : {}]) \cup {[a |-> 0]}
Next == x' = [a |-> 0] \/ x' = [a |-> 2]
Alias == Next
Weak == Init /\ [][Next]_x /\ WF_x(Next)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Alias)
Live == <>[](x = [a |-> 0])
====
