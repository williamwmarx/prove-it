---- MODULE SubsetEmpty ----
EXTENDS Naturals
VARIABLE x
Init == x = {}
Next == x' \in SUBSET [a : {}] \/ x' = {1}
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Live == []<>(x = {})
====
