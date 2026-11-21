---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Next == x < 2 /\ x' = x + 1
Spec == x = 0 /\ [][Next]_x /\ WF_x(Next)
Ignore(F(_),n) == x=2
Prop == [](Ignore(LAMBDA v : x'=v, x'))
====
