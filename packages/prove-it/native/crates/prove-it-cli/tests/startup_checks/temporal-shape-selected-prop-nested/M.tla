---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x=0
Next == x<2 /\ x'=x+1
Alias==L::(K::[](x<1))
Spec == Init /\ [][Next]_x /\ WF_x(Next)
Prop == Alias!L!K
====
