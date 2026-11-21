---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x=0
Next == x<2 /\ x'=x+1
Alias==L::[Next]_x
Spec == Init /\ [][Next]_x
Prop == Alias!L
====
