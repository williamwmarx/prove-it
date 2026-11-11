---- MODULE PostconditionConstantLiveness ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Visits == []<>(x = 0)
Never == FALSE
====
