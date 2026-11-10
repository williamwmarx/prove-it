---- MODULE MProductRcdKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = [a |-> <<0, 1>>]
Next == x' \in [a : ({1, 3} \X {1})] \/ x' = [a |-> <<0, 1>>] \/ x' = [a |-> <<2, 1>>]
Alias == Next
Weak == Init /\ [][Next]_x /\ WF_x(Next)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Alias)
Live == []<>(x = [a |-> <<0, 1>>])
====
