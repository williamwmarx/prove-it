---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x=0
Next == x<3 /\ PrintT([[a |-> x] EXCEPT !.b = 1 \div 0]) /\ x'=x+1
====
