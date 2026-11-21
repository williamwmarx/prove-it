---- MODULE M ----
EXTENDS Naturals,TLC
VARIABLE x
Init == x=0
Next == x=1 /\ x'=2
Alias == [visible |-> Print("alias", [ [a |-> x] EXCEPT !.z = PrintT("rhs") ])]
====
