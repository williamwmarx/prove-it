---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x=0
Next == x<2 /\ [[a |-> x] EXCEPT !.b = 1 \div 0].a = x /\ x'=x+1
Inv == x<1
====
