---- MODULE M ----
EXTENDS Naturals,TLC
VARIABLE x
Init == x=0
Next == x=0 /\ PrintT("before") /\ ([ [a |-> 1] EXCEPT !.z = PrintT("rhs") ] = [a |-> 1]) /\ x'=1 /\ PrintT("after")
Inv == x=0
====
