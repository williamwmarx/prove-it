---- MODULE M ----
EXTENDS Integers
VARIABLE x
D[k \in Nat] == [[a |-> k] EXCEPT !.b = 0]
Init == x=0
Next == x'=x
====
