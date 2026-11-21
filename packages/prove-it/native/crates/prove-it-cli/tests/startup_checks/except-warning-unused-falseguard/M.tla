---- MODULE M ----
EXTENDS Integers
VARIABLE x
D == IF FALSE THEN [[a |-> 1] EXCEPT !.b = 0] ELSE 1
Init == x=0
Next == x'=x
====
