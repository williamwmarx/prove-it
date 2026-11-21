---- MODULE M ----
EXTENDS Naturals, Integers, TLC
VARIABLE x
Next == x < 2 /\ x' = x + 1
Spec == x = 0 /\ [][Next]_x /\ WF_x(Next)
Over(F(_),n) == ENABLED F(n)
Prop == <>(Over(LAMBDA v : x=v /\ x'=v, PrintT(2)))
====
