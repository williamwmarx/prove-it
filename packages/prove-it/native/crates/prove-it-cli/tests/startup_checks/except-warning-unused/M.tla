---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
D == [[a |-> 1] EXCEPT !.b = 1 \div 0]
Init == x=0
Next == x'=x
====
