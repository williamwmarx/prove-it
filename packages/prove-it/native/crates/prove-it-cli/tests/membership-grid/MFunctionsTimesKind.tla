---- MODULE MFunctionsTimesKind ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
D == {1, 3}
Init == x = <<[i \in {1} |-> 0], 1>>
Next == x' \in ([{1} -> {1, 3}]) \X {1} \/ x' = <<[i \in {1} |-> 0], 1>> \/ x' = <<[i \in {1} |-> 2], 1>>
Alias == Next
Weak == Init /\ [][Next]_x /\ WF_x(Next)
AliasWeak == Init /\ [][Next]_x /\ WF_x(Alias)
Live == []<>(x = <<[i \in {1} |-> 0], 1>>)
====
