---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x=0
Next == x<2 /\ x'=x+1
Inv==TRUE
Machine(i,n)==i /\ [][n]_x
Spec == Machine(Init,Next)
====
