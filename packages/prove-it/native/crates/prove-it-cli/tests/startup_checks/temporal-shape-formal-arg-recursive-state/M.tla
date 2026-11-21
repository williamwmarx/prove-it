---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init==x=0
Next==x<2 /\ x'=x+1
Actual(a)==x'=a
Machine(i,n(_))==LET RECURSIVE R(_) R(k)==IF k=0 THEN x ELSE R(k-1) IN i /\ [][n(R(0))]_x
Spec==Machine(Init,Actual)
====
