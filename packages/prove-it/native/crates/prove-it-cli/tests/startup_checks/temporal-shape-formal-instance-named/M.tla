---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init==x=0
Next==x<2 /\ x'=x+1
I==INSTANCE B WITH C<-0,y<-x
Spec==I!Machine(Init,Next)
====
