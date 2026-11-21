---- MODULE M ----
EXTENDS Integers
VARIABLE x
RECURSIVE F(_)
F(n) == IF n=0 THEN [[a |-> n] EXCEPT !.b = 0] ELSE F(n-1)
ASSUME F(1) = F(1)
Init == x=0
Next == x'=x
====
