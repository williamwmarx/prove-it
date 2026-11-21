---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x=0
Next == x<2 /\ x'=x+1
Id(a) == a
Spec == Init /\ Id(Id(Next))
====
