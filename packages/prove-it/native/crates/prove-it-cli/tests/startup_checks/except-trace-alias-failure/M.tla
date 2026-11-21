---- MODULE M ----
EXTENDS Naturals,TLC
VARIABLE x
Init == x=0
Next == x=0 /\ x'=1
Inv == x=0
Alias == PrintT("before-alias") /\ ([ [a |-> x] EXCEPT !.z = PrintT("rhs") ] = [a |-> x]) /\ (IF 1 THEN TRUE ELSE FALSE)
====
