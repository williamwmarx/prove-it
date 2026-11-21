---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x=0
Next == x<2 /\ x'=x+1

Machine(i,n)==i /\ [][n]_<<>>
Spec == Machine(Init,Next)
====
