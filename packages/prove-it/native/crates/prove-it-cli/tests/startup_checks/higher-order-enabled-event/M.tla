---- MODULE M ----
EXTENDS Naturals, Integers
VARIABLE x
Next == x < 2 /\ x' = x + 1
Spec == x = 0 /\ [][Next]_x /\ WF_x(Next)
Over(Op(_)) == ENABLED Op(2)
Prop == <>(Over(LAMBDA n : x = n /\ x' = n))
====
