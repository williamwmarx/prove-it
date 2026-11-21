---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x=0
Next == x<2 /\ x'=x+1

Spec == Init /\ [][Next]_x /\ WF_x(Next)
Prop == L::[](x<1)
====
