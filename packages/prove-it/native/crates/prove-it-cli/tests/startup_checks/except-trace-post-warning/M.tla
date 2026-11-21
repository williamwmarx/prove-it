---- MODULE M ----
EXTENDS Naturals,TLC
VARIABLE x
Init == x=0
Next == x=0 /\ x'=1
Post == TLCGet("distinct")=2 /\ PrintT("post-before") /\ ([ [a |-> 1] EXCEPT !.z = PrintT("rhs") ] = [a |-> 1]) /\ PrintT("post-after")
====
