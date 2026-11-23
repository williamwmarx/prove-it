---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Next == x < 2 /\ x' = x + 1
Spec == x = 0 /\ [][Next]_x /\ WF_x(Next)
RECURSIVE Reach(_)
Reach(n) == IF x = 0 THEN <>(x = 2) ELSE Reach(n + 1)
Prop == <>(x = 2) /\ Reach(1)
====

