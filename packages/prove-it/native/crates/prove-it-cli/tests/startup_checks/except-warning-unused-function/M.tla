---- MODULE M ----
EXTENDS Integers
VARIABLE x
D[k \in {1,2}] == [[a |-> k] EXCEPT !.b = 0]
Init == x=0
Next == x'=x
====
