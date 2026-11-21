---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init==x=0
Next==x<2 /\ x'=x+1
Actual(a)==x'=a
Machine(i,n(_))==LET L==x IN i /\ [][n(L)]_x
Spec==Machine(Init,Actual)
====
