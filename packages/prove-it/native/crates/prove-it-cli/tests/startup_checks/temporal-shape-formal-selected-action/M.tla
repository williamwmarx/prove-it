---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init==x=0
Next==x<2 /\ x'=x+1
Alias(n)==L::n
Machine(i,n)==i /\ [][Alias(n)!L]_x
Spec==Machine(Init,Next)
====
