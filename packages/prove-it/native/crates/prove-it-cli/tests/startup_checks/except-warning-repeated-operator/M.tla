---- MODULE M ----
EXTENDS Integers
VARIABLE x
F(n) == [[a |-> n] EXCEPT !.b = 0]
ASSUME F(1) = F(1)
Init == x=0
Next == x'=x
====
