---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
ASSUME [[a |-> 1] EXCEPT !.b[1 \div 0] = Print(99,0)] = [a |-> 1]
Init == x=0
Next == x'=x
====
