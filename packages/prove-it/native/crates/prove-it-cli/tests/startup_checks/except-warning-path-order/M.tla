---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
ASSUME PrintT([[a |-> [b |-> 1]] EXCEPT !.missing[Print(11,"c")] = Print(99,0)])
Init == x=0
Next == x'=x
====
