---- MODULE UnionEmpty ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' \in ([a : {}] \cup {1}) \/ x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Live == []<>(x = 2)
====
