---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Fair == LET RECURSIVE F F == F /\ WF_x(Next) IN Init /\ [][Next]_x /\ F
Prop == <>(x = 1)
====
