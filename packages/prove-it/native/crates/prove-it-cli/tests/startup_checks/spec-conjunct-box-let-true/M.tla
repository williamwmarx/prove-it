---- MODULE M ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
Init == x=0
Next == x<2 /\ x'=x+1
Id(a) == a
Spec == Init /\ [](LET A == TRUE IN A) /\ [][Next]_x
====
