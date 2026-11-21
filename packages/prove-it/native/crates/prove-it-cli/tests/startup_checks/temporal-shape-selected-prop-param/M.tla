---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x=0
Next == x<2 /\ x'=x+1
Alias(a)==L(a)::[](x<a)
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Prop == Alias(1)!L(1)
====
