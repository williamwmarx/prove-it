---- MODULE M ----
EXTENDS Naturals
CONSTANT C
VARIABLE x
Init == x=0
Next == x<2 /\ x'=x+1
No == FALSE
Spec == Init /\ [][Next]_x
Prop == No /\ x=0
====
