---- MODULE SubseteqEmpty ----
EXTENDS Naturals
VARIABLE x
Init == x = {0}
Next == x' \subseteq [a : {}] \/ x' = (IF x = {0} THEN {1} ELSE {0})
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Live == []<>(x = {0})
====
