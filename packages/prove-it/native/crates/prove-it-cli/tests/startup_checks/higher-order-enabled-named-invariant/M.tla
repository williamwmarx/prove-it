---- MODULE M ----
EXTENDS Naturals, Integers
VARIABLE x
Next == x < 2 /\ x' = x + 1
Spec == x = 0 /\ [][Next]_x /\ WF_x(Next)
Op(n) == x = n /\ x' = n
Over(F(_)) == ENABLED F(2)
Prop == [](Over(Op))
====
