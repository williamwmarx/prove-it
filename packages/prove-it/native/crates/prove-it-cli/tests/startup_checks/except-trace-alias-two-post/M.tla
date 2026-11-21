---- MODULE M ----
EXTENDS Naturals,TLC
VARIABLE x
Init == x=0
Next == x=0 /\ x'=1
Inv == x=0
Alias == [visible |-> Print("alias", [ [a |-> x] EXCEPT !.z = PrintT("rhs") ])]
P == TLCGet("distinct")=2 /\ PrintT("P")
Q == TLCGet("distinct")=2 /\ PrintT("Q")
====
