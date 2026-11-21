---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init==x=0
Next==x<2 /\ x'=x+1
I==INSTANCE B
Spec==I!Machine(Init,Next)
====
