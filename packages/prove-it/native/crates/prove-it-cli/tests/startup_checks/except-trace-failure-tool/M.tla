---- MODULE M ----
EXTENDS Naturals,TLC
VARIABLE x
Init == x=0
Next == PrintT("before") /\ ([ [a |-> 1] EXCEPT !.z = PrintT("rhs") ] = [a |-> 1]) /\ x'=IF 1 THEN 1 ELSE 0
====
