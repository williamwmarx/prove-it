---- MODULE EmptyRecords ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' \in [a : {}] \/ x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Live == []<>(x = 2)
====
