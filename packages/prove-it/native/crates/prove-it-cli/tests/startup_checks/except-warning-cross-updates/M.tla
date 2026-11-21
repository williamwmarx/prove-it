---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
ASSUME PrintT([[a |-> 1] EXCEPT !.b = Print(99,0), !.a = @+1, !.b = 1 \div 0, !.a = @+1])
Init == x=0
Next == x'=x
====
