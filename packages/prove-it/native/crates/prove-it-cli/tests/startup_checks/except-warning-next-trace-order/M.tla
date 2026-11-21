---- MODULE M ----
EXTENDS Integers, Sequences
VARIABLE x
Init == x=0
Next == x<1 /\ x'=[[a |-> x+1] EXCEPT !.b=0].a
Inv == x<1
====
